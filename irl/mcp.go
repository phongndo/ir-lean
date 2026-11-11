package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
)

// The MCP versions this server speaks, newest first. A client asking for one of them gets it, and any other
// gets the newest, as the specification says. Only tools are served, which each of these has.
var protocolVersions = []string{"2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"}

const version = "0.1.0"

const instructions = `irl checks claims about functions in LLVM IR with Lean, in ir-lean's model of LLVM IR.
Every answer is the JSON its tool prints, with a status and a reason. Only verify_check's "proved" says a claim
holds, and only as its claim.statement and assumptions say. ptf_run's "passed_tier1" is a test, not a proof.
unsupported, timeout and unknown decide nothing. Paths are absolute, or relative to %s.`

// JSON-RPC's error codes.
const (
	parseError     = -32700
	invalidRequest = -32600
	methodNotFound = -32601
	invalidParams  = -32602
)

// server serves the tools over MCP's stdio transport: one JSON-RPC message a line, on stdin and stdout.
// irl decides no verdict. A tool's answer is what it printed, and the call's result carries it unchanged.
type server struct {
	root string
	// Where the tools run, and so what relative paths in a request are relative to.
	base  string
	tools []*mcpTool
	// One token for each tool that may run Lean at once.
	slots chan struct{}
	// How long a cancelled tool has to stop before it's killed.
	grace time.Duration
	// How often a call with a progress token is told it's still running.
	every time.Duration

	outMu sync.Mutex
	out   io.Writer

	mu    sync.Mutex
	calls map[string]*call
	wg    sync.WaitGroup
}

type call struct {
	cancel    context.CancelFunc
	cancelled atomic.Bool
}

// newServer reads each tool's contract, for its schemas. It fails if any can't be read, since a tool whose
// contract can't be read can't be run.
func newServer(ctx context.Context, root, base string, jobs int, out io.Writer) (*server, error) {
	contracts, err := capabilities(ctx, root)
	if err != nil {
		return nil, err
	}
	entries := contracts["commands"].(map[string]any)
	s := &server{
		root:  root,
		base:  base,
		tools: newTools(),
		slots: make(chan struct{}, max(jobs, 1)),
		grace: 10 * time.Second,
		every: 15 * time.Second,
		out:   out,
		calls: map[string]*call{},
	}
	for _, t := range s.tools {
		if t.fromContract == nil {
			continue
		}
		contract, _ := entries[t.command].(map[string]any)["capabilities"].(map[string]any)
		if err := t.fromContract(t, contract); err != nil {
			return nil, fmt.Errorf("%s: %w", t.Name, err)
		}
	}
	return s, nil
}

// serve answers messages from in until it's closed or ctx is done, then cancels every call still running and
// waits for each to stop.
func (s *server) serve(ctx context.Context, in io.Reader) error {
	lines := make(chan []byte)
	failed := make(chan error, 1)
	stop := make(chan struct{})
	defer close(stop)
	go func() {
		r := bufio.NewReaderSize(in, 1<<20)
		for {
			line, err := r.ReadBytes('\n')
			if len(bytes.TrimSpace(line)) > 0 {
				select {
				case lines <- line:
				case <-stop:
					return
				}
			}
			if err != nil {
				failed <- err
				return
			}
		}
	}()
	defer s.shutdown()
	for {
		select {
		case <-ctx.Done():
			return nil
		case line := <-lines:
			s.handle(ctx, line)
		case err := <-failed:
			if errors.Is(err, io.EOF) {
				return nil
			}
			return err
		}
	}
}

func (s *server) shutdown() {
	s.mu.Lock()
	for _, c := range s.calls {
		c.cancel()
	}
	s.mu.Unlock()
	s.wg.Wait()
}

type message struct {
	JSONRPC string          `json:"jsonrpc"`
	ID      json.RawMessage `json:"id"`
	Method  string          `json:"method"`
	Params  json.RawMessage `json:"params"`
}

func (s *server) handle(ctx context.Context, line []byte) {
	var m message
	if err := json.Unmarshal(line, &m); err != nil {
		code := parseError
		if json.Valid(line) {
			// JSON, but not one message: a batch, which MCP no longer has, or not an object.
			code = invalidRequest
		}
		s.fail(json.RawMessage("null"), code, err.Error())
		return
	}
	notification := m.ID == nil
	if m.JSONRPC != "2.0" || bytes.Equal(m.ID, []byte("null")) {
		if !notification {
			s.fail(m.ID, invalidRequest, `a request has "jsonrpc": "2.0" and an id that isn't null`)
		}
		return
	}
	switch m.Method {
	case "initialize":
		s.reply(m.ID, s.initialize(m.Params))
	case "ping":
		s.reply(m.ID, struct{}{})
	case "tools/list":
		s.reply(m.ID, map[string]any{"tools": s.tools})
	case "tools/call":
		s.call(ctx, m)
	case "notifications/cancelled":
		s.cancelled(m.Params)
	case "":
		// A response: this server sends no requests, so there's nothing it answers.
	default:
		if !notification {
			s.fail(m.ID, methodNotFound, "irl serves tools only: no method "+strconv.Quote(m.Method))
		}
	}
}

func (s *server) initialize(params json.RawMessage) map[string]any {
	var p struct {
		ProtocolVersion string `json:"protocolVersion"`
	}
	_ = json.Unmarshal(params, &p)
	v := protocolVersions[0]
	if slices.Contains(protocolVersions, p.ProtocolVersion) {
		v = p.ProtocolVersion
	}
	return map[string]any{
		"protocolVersion": v,
		"capabilities":    map[string]any{"tools": map[string]any{"listChanged": false}},
		"serverInfo":      map[string]any{"name": "irl", "title": "ir-lean", "version": version},
		"instructions":    fmt.Sprintf(instructions, s.base),
	}
}

func (s *server) call(ctx context.Context, m message) {
	var p struct {
		Name      string          `json:"name"`
		Arguments json.RawMessage `json:"arguments"`
		Meta      struct {
			ProgressToken json.RawMessage `json:"progressToken"`
		} `json:"_meta"`
	}
	if err := json.Unmarshal(m.Params, &p); err != nil {
		s.fail(m.ID, invalidParams, err.Error())
		return
	}
	i := slices.IndexFunc(s.tools, func(t *mcpTool) bool { return t.Name == p.Name })
	if i < 0 {
		s.fail(m.ID, invalidParams, "no tool "+strconv.Quote(p.Name))
		return
	}
	arguments := bytes.TrimSpace(p.Arguments)
	if len(arguments) == 0 || bytes.Equal(arguments, []byte("null")) {
		arguments = []byte("{}")
	}
	if arguments[0] != '{' {
		s.fail(m.ID, invalidParams, "arguments must be an object")
		return
	}
	ctx, cancel := context.WithCancel(ctx)
	c := &call{cancel: cancel}
	key := string(m.ID)
	s.mu.Lock()
	s.calls[key] = c
	s.mu.Unlock()
	s.wg.Go(func() {
		defer func() {
			cancel()
			s.mu.Lock()
			if s.calls[key] == c {
				delete(s.calls, key)
			}
			s.mu.Unlock()
		}()
		result := s.run(ctx, s.tools[i], arguments, p.Meta.ProgressToken)
		// A cancelled request gets no response, as MCP says, and nor does one cut off by shutting down.
		if c.cancelled.Load() || ctx.Err() != nil {
			return
		}
		s.reply(m.ID, result)
	})
}

func (s *server) cancelled(params json.RawMessage) {
	var p struct {
		RequestID json.RawMessage `json:"requestId"`
	}
	if json.Unmarshal(params, &p) != nil {
		return
	}
	s.mu.Lock()
	c := s.calls[string(bytes.TrimSpace(p.RequestID))]
	s.mu.Unlock()
	if c != nil {
		c.cancelled.Store(true)
		c.cancel()
	}
}

// run runs one tool call to its result, or to nothing if it's cancelled.
func (s *server) run(ctx context.Context, t *mcpTool, arguments json.RawMessage, token json.RawMessage) map[string]any {
	if t.command == "" {
		caps, err := capabilities(ctx, s.root)
		text, _ := json.Marshal(caps)
		return result(text, caps, err != nil)
	}
	c, _ := findCommand(commands, t.command)
	argv, stdin, err := t.argv(arguments)
	if err != nil {
		return result([]byte(err.Error()), nil, true)
	}
	state := &atomic.Value{}
	state.Store("waiting for a job slot")
	defer s.progress(ctx, token, state)()
	if t.heavy {
		select {
		case s.slots <- struct{}{}:
			defer func() { <-s.slots }()
		case <-ctx.Done():
			return nil
		}
	}
	state.Store("running " + c.path)
	r := runTool(ctx, s.base, append([]string{filepath.Join(s.root, c.path)}, argv...), stdin, s.grace)
	switch {
	case r.cancelled:
		return nil
	case r.err != nil:
		return result([]byte(fmt.Sprintf("%s didn't start: %v", c.path, r.err)), nil, true)
	}
	answer := bytes.TrimSpace(r.stdout)
	var structured map[string]any
	if json.Unmarshal(answer, &structured) != nil || structured == nil {
		text := fmt.Sprintf("%s printed no JSON answer, and exited %d. Its stderr ends:\n%s", c.path, r.exit,
			bytes.TrimSpace(r.stderr))
		return result([]byte(text), nil, true)
	}
	// An answer saying the request or the tool failed is an error the caller may fix. Every other status is
	// an answer, a counterexample or unknown included.
	failed := structured["status"] == "error" || slices.Contains([]any{"invalid_request", "internal_error"},
		structured["reason"])
	return result(answer, structured, failed)
}

// result is a tool call's result: the answer as text, exactly as the tool printed it, and as structured
// content, which MCP since 2025-06-18 checks against the tool's output schema.
func result(text []byte, structured map[string]any, isError bool) map[string]any {
	r := map[string]any{
		"content": []map[string]any{{"type": "text", "text": string(text)}},
		"isError": isError,
	}
	if structured != nil {
		r["structuredContent"] = structured
	}
	return r
}

// progress tells a call that asked for progress that it's still running, every s.every, until the returned
// function is called. MCP's progress only has to increase, so it's the seconds the call has run.
func (s *server) progress(ctx context.Context, token json.RawMessage, state *atomic.Value) func() {
	if len(token) == 0 || s.every <= 0 {
		return func() {}
	}
	done := make(chan struct{})
	started := time.Now()
	go func() {
		ticker := time.NewTicker(s.every)
		defer ticker.Stop()
		for {
			select {
			case <-done:
				return
			case <-ctx.Done():
				return
			case <-ticker.C:
				seconds := time.Since(started).Seconds()
				s.send(map[string]any{
					"jsonrpc": "2.0",
					"method":  "notifications/progress",
					"params": map[string]any{
						"progressToken": token,
						"progress":      seconds,
						"message":       fmt.Sprintf("%s, %.0f s in", state.Load(), seconds),
					},
				})
			}
		}
	}()
	return func() { close(done) }
}

func (s *server) reply(id json.RawMessage, result any) {
	s.send(map[string]any{"jsonrpc": "2.0", "id": id, "result": result})
}

func (s *server) fail(id json.RawMessage, code int, text string) {
	s.send(map[string]any{"jsonrpc": "2.0", "id": id, "error": map[string]any{"code": code, "message": text}})
}

// send writes one message on one line. Nothing else goes to stdout.
func (s *server) send(message map[string]any) {
	line, err := json.Marshal(message)
	if err != nil {
		fmt.Fprintf(os.Stderr, "irl mcp: can't send a message: %v\n", err)
		return
	}
	s.outMu.Lock()
	defer s.outMu.Unlock()
	_, _ = s.out.Write(append(line, '\n'))
}

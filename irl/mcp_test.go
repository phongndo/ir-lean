package main

import (
	"bufio"
	"context"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"
)

// A checkout with stub tools, in shell, that answer as the real ones do, from what they're sent. No Lean.
func stubRoot(t *testing.T) string {
	t.Helper()
	root := t.TempDir()
	write := func(path, text string, mode os.FileMode) {
		t.Helper()
		path = filepath.Join(root, path)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), mode); err != nil {
			t.Fatal(err)
		}
	}
	write("lakefile.toml", "", 0o644)
	write("build/ir-lean", "#!/bin/sh\n", 0o755)
	contract := func(schema string, statuses, fields []string) string {
		c := map[string]any{"schema": schema, "statuses": map[string]string{}, "request_fields": map[string]string{}}
		properties := map[string]any{}
		for _, s := range statuses {
			c["statuses"].(map[string]string)[s] = s
		}
		for _, f := range fields {
			c["request_fields"].(map[string]string)[f] = f
			properties[f] = map[string]any{"description": f}
		}
		c["request_json_schema"] = map[string]any{"type": "object", "properties": properties}
		text, _ := json.Marshal(c)
		return string(text)
	}
	write("tools/verify.caps", contract("ir-lean.verify/1", []string{"proved", "error"}, []string{"input", "function"}), 0o644)
	write("tools/prooftest/prooftest.caps", contract("ir-lean.prooftest/1", []string{"passed_tier1", "unknown"},
		[]string{"statement"}), 0o644)
	write("tools/store/store.caps", `{"schema": "ir-lean.store/1", "schemas": {"lookup": "ir-lean.store.lookup/1"}}`, 0o644)
	// What each request asks of the stub: to wait until it's interrupted, to hold a job slot for a moment, to
	// fail, or to print something that isn't JSON. Anything else is proved, with the request and the
	// directory it ran in.
	answer := `#!/bin/sh
here=$(dirname "$0")
case "$1" in
capabilities) cat "$here/$(basename "$0" .py).caps"; exit 0 ;;
esac
request=$(cat)
case "$request" in
*wait*)
	sleep 30 &
	trap 'kill $!; echo interrupted >"$IRL_TEST_DIR/interrupted"; exit 130' INT
	echo started >"$IRL_TEST_DIR/started"
	wait
	exit 0 ;;
*hold*)
	echo start >>"$IRL_TEST_DIR/log"; sleep 0.3; echo end >>"$IRL_TEST_DIR/log" ;;
*fail*) echo '{"schema": "ir-lean.verify/1", "status": "error", "reason": "invalid_request"}'; exit 1 ;;
*garbage*) echo 'not JSON'; echo 'it broke' >&2; exit 1 ;;
esac
printf '{"schema": "ir-lean.verify/1", "status": "proved", "request": %s, "cwd": "%s"}\n' "$request" "$PWD"
`
	write("tools/verify.py", answer, 0o755)
	write("tools/prooftest/prooftest.py", answer, 0o755)
	write("tools/store/store.py", `#!/bin/sh
case "$1" in
capabilities) cat "$(dirname "$0")/store.caps"; exit 0 ;;
esac
printf '{"schema": "ir-lean.store.lookup/1", "status": "none", "argv": "%s"}\n' "$*"
exit 3
`, 0o755)
	return root
}

// session is an MCP client talking to a server.
type session struct {
	t        *testing.T
	in       io.WriteCloser
	messages chan map[string]any
}

func newSession(t *testing.T, in io.WriteCloser, out io.Reader) *session {
	s := &session{t: t, in: in, messages: make(chan map[string]any, 100)}
	go func() {
		scanner := bufio.NewScanner(out)
		scanner.Buffer(nil, 1<<26)
		for scanner.Scan() {
			var m map[string]any
			if err := json.Unmarshal(scanner.Bytes(), &m); err != nil {
				t.Errorf("the server sent a line that isn't JSON: %q", scanner.Text())
				continue
			}
			s.messages <- m
		}
		close(s.messages)
	}()
	return s
}

// served is closed when the server stops serving, with what serve returned in err.
type served struct {
	done chan struct{}
	err  error
}

// startServer serves a stub checkout in this process, and closes it at the end of the test.
func startServer(t *testing.T, root string, jobs int, configure func(*server)) (*session, *served) {
	t.Helper()
	t.Setenv("IRL_TEST_DIR", t.TempDir())
	inR, inW := io.Pipe()
	outR, outW := io.Pipe()
	s, err := newServer(context.Background(), root, root, jobs, outW)
	if err != nil {
		t.Fatal(err)
	}
	if configure != nil {
		configure(s)
	}
	end := &served{done: make(chan struct{})}
	go func() {
		end.err = s.serve(context.Background(), inR)
		outW.Close()
		close(end.done)
	}()
	t.Cleanup(func() { inW.Close(); <-end.done })
	return newSession(t, inW, outR), end
}

func (s *session) send(message any) {
	s.t.Helper()
	line, err := json.Marshal(message)
	if err != nil {
		s.t.Fatal(err)
	}
	if _, err := s.in.Write(append(line, '\n')); err != nil {
		s.t.Fatal(err)
	}
}

// next is the next message the server sends, within a minute.
func (s *session) next() map[string]any {
	s.t.Helper()
	select {
	case m, ok := <-s.messages:
		if !ok {
			s.t.Fatal("the server closed its output")
		}
		return m
	case <-time.After(time.Minute):
		s.t.Fatal("no message from the server in a minute")
		return nil
	}
}

// request sends a request and returns its response, failing on anything else first.
func (s *session) request(id any, method string, params any) map[string]any {
	s.t.Helper()
	s.send(map[string]any{"jsonrpc": "2.0", "id": id, "method": method, "params": params})
	m := s.next()
	if got, _ := json.Marshal(m["id"]); string(got) != string(must(json.Marshal(id))) {
		s.t.Fatalf("the response to %v is to %v: %v", id, m["id"], m)
	}
	return m
}

func (s *session) call(id any, tool string, arguments any) map[string]any {
	s.t.Helper()
	m := s.request(id, "tools/call", map[string]any{"name": tool, "arguments": arguments})
	result, ok := m["result"].(map[string]any)
	if !ok {
		s.t.Fatalf("calling %s gave no result: %v", tool, m)
	}
	return result
}

func must[T any](v T, err error) T {
	if err != nil {
		panic(err)
	}
	return v
}

func TestInitializeAgreesOnAVersion(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	for _, c := range []struct{ asked, got string }{
		{"2025-06-18", "2025-06-18"},
		{"2024-11-05", "2024-11-05"},
		{"1999-01-01", protocolVersions[0]},
	} {
		r := s.request(1, "initialize", map[string]any{"protocolVersion": c.asked})["result"].(map[string]any)
		if r["protocolVersion"] != c.got {
			t.Errorf("asked for %s, got %v, not %s", c.asked, r["protocolVersion"], c.got)
		}
		if r["serverInfo"].(map[string]any)["name"] != "irl" || r["capabilities"].(map[string]any)["tools"] == nil {
			t.Errorf("initialize says %v", r)
		}
	}
	if s.request(2, "ping", nil)["result"] == nil {
		t.Error("ping has no result")
	}
}

func TestToolsTakeTheirSchemasFromTheContracts(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	tools := s.request(1, "tools/list", nil)["result"].(map[string]any)["tools"].([]any)
	byName := map[string]map[string]any{}
	for _, tool := range tools {
		byName[tool.(map[string]any)["name"].(string)] = tool.(map[string]any)
	}
	for name, fields := range map[string][]string{"verify_check": {"function", "input"}, "ptf_run": {"statement"}} {
		properties := byName[name]["inputSchema"].(map[string]any)["properties"].(map[string]any)
		if got := slices.Sorted(func(yield func(string) bool) {
			for k := range properties {
				yield(k)
			}
		}); !slices.Equal(got, fields) {
			t.Errorf("%s takes %v, not %v", name, got, fields)
		}
	}
	status := byName["verify_check"]["outputSchema"].(map[string]any)["properties"].(map[string]any)["status"]
	if got := must(json.Marshal(status)); string(got) != `{"enum":["error","proved"]}` {
		t.Errorf("verify_check's statuses are %s", got)
	}
	if len(byName) != 4 || byName["capabilities"] == nil || byName["store_lookup"] == nil {
		t.Errorf("tools/list gives %v", tools)
	}
	if !byName["verify_check"]["annotations"].(map[string]any)["readOnlyHint"].(bool) {
		t.Error("verify_check isn't read-only")
	}
}

func TestACallSendsItsArgumentsAsTheRequest(t *testing.T) {
	root := stubRoot(t)
	s, _ := startServer(t, root, 1, nil)
	arguments := map[string]any{"input": map[string]any{"ir": "a.ll"}, "function": "f"}
	r := s.call(1, "verify_check", arguments)
	answer := r["structuredContent"].(map[string]any)
	if r["isError"] != false || answer["status"] != "proved" {
		t.Fatalf("got %v", r)
	}
	if got, want := must(json.Marshal(answer["request"])), must(json.Marshal(arguments)); string(got) != string(want) {
		t.Errorf("the tool was sent %s, not %s", got, want)
	}
	if answer["cwd"] != root {
		t.Errorf("the tool ran in %v, not %s", answer["cwd"], root)
	}
	// The text is the answer exactly as the tool printed it.
	text := r["content"].([]any)[0].(map[string]any)["text"].(string)
	if !strings.HasPrefix(text, `{"schema": "ir-lean.verify/1", "status": "proved"`) {
		t.Errorf("the text is %q", text)
	}
	if s.call(2, "ptf_run", map[string]any{"statement": "x"})["structuredContent"].(map[string]any)["status"] != "proved" {
		t.Error("ptf_run didn't run")
	}
}

func TestAFailedRequestOrToolIsAnError(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	r := s.call(1, "verify_check", map[string]any{"fail": true})
	if r["isError"] != true || r["structuredContent"].(map[string]any)["reason"] != "invalid_request" {
		t.Errorf("a request the tool refused gave %v", r)
	}
	r = s.call(2, "verify_check", map[string]any{"garbage": true})
	text := r["content"].([]any)[0].(map[string]any)["text"].(string)
	if r["isError"] != true || r["structuredContent"] != nil || !strings.Contains(text, "it broke") ||
		!strings.Contains(text, "exited 1") {
		t.Errorf("a tool that printed no JSON gave %v", r)
	}
}

func TestProtocolErrors(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	code := func(m map[string]any) float64 {
		t.Helper()
		e, ok := m["error"].(map[string]any)
		if !ok {
			t.Fatalf("no error in %v", m)
		}
		return e["code"].(float64)
	}
	for _, c := range []struct {
		line string
		code float64
	}{
		{"{not json", parseError},
		{`[{"jsonrpc": "2.0", "id": 1, "method": "ping"}]`, invalidRequest},
		{`{"jsonrpc": "2.0", "id": null, "method": "ping"}`, invalidRequest},
		{`{"jsonrpc": "2.0", "id": 1, "method": "resources/list"}`, methodNotFound},
		{`{"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "nope"}}`, invalidParams},
		{`{"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "verify_check", "arguments": [1]}}`,
			invalidParams},
	} {
		if _, err := s.in.Write([]byte(c.line + "\n")); err != nil {
			t.Fatal(err)
		}
		if got := code(s.next()); got != c.code {
			t.Errorf("%s gave error %v, not %v", c.line, got, c.code)
		}
	}
	// A notification gets no answer, so the next message is the ping's.
	s.send(map[string]any{"jsonrpc": "2.0", "method": "notifications/whatever"})
	if m := s.request("p", "ping", nil); m["error"] != nil {
		t.Errorf("ping gave %v", m)
	}
}

func waitFor(t *testing.T, path string) {
	t.Helper()
	for start := time.Now(); time.Since(start) < 30*time.Second; time.Sleep(20 * time.Millisecond) {
		if _, err := os.Stat(path); err == nil {
			return
		}
	}
	t.Fatalf("%s never appeared", path)
}

func TestCancellingACallInterruptsItsTool(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	dir := os.Getenv("IRL_TEST_DIR")
	s.send(map[string]any{"jsonrpc": "2.0", "id": 7, "method": "tools/call",
		"params": map[string]any{"name": "verify_check", "arguments": map[string]any{"wait": true}}})
	waitFor(t, filepath.Join(dir, "started"))
	s.send(map[string]any{"jsonrpc": "2.0", "method": "notifications/cancelled", "params": map[string]any{"requestId": 7}})
	waitFor(t, filepath.Join(dir, "interrupted"))
	// The cancelled call gets no response, and the server goes on answering.
	if m := s.request(8, "ping", nil); m["error"] != nil {
		t.Errorf("ping after a cancel gave %v", m)
	}
}

func TestClosingStdinStopsEveryCall(t *testing.T) {
	s, end := startServer(t, stubRoot(t), 1, nil)
	dir := os.Getenv("IRL_TEST_DIR")
	s.send(map[string]any{"jsonrpc": "2.0", "id": 1, "method": "tools/call",
		"params": map[string]any{"name": "verify_check", "arguments": map[string]any{"wait": true}}})
	waitFor(t, filepath.Join(dir, "started"))
	s.in.Close()
	select {
	case <-end.done:
		if end.err != nil {
			t.Fatal(end.err)
		}
	case <-time.After(30 * time.Second):
		t.Fatal("the server didn't stop")
	}
	waitFor(t, filepath.Join(dir, "interrupted"))
	for m := range s.messages {
		t.Errorf("a call cut off by closing stdin was answered: %v", m)
	}
}

func TestStoreLookupMapsArgumentsToFlags(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	r := s.call(1, "store_lookup", map[string]any{"statement": "a = a", "imports": []string{"M", "N"}})
	if got := r["structuredContent"].(map[string]any)["argv"]; got != "lookup --statement a = a --import M --import N --json" {
		t.Errorf("the store was run with %v", got)
	}
	// Exit 3, nothing found, is an answer, not an error.
	if r["isError"] != false {
		t.Errorf("a lookup that found nothing is an error: %v", r)
	}
	for _, bad := range []map[string]any{{"statement": "a", "other": 1}, {"imports": []string{"M"}}} {
		if r := s.call(2, "store_lookup", bad); r["isError"] != true || r["structuredContent"] != nil {
			t.Errorf("%v gave %v", bad, r)
		}
	}
}

func TestProgressWhileACallRuns(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, func(s *server) { s.every = 50 * time.Millisecond })
	dir := os.Getenv("IRL_TEST_DIR")
	s.send(map[string]any{"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": map[string]any{
		"name": "verify_check", "arguments": map[string]any{"wait": true}, "_meta": map[string]any{"progressToken": "tok"}}})
	waitFor(t, filepath.Join(dir, "started"))
	last := -1.0
	for range 3 {
		m := s.next()
		p := m["params"].(map[string]any)
		if m["method"] != "notifications/progress" || p["progressToken"] != "tok" || p["progress"].(float64) <= last {
			t.Fatalf("got %v", m)
		}
		last = p["progress"].(float64)
	}
	s.send(map[string]any{"jsonrpc": "2.0", "method": "notifications/cancelled", "params": map[string]any{"requestId": 1}})
	waitFor(t, filepath.Join(dir, "interrupted"))
}

func TestCallsUsingLeanWaitForAJobSlot(t *testing.T) {
	s, _ := startServer(t, stubRoot(t), 1, nil)
	dir := os.Getenv("IRL_TEST_DIR")
	for id := range 3 {
		s.send(map[string]any{"jsonrpc": "2.0", "id": id, "method": "tools/call",
			"params": map[string]any{"name": "verify_check", "arguments": map[string]any{"hold": true}}})
	}
	for range 3 {
		if m := s.next(); m["result"] == nil {
			t.Fatalf("got %v", m)
		}
	}
	log := string(must(os.ReadFile(filepath.Join(dir, "log"))))
	if log != strings.Repeat("start\nend\n", 3) {
		t.Errorf("with one slot, the calls overlapped:\n%s", log)
	}
}

func TestCommandLine(t *testing.T) {
	t.Setenv("IRL_ROOT", stubRoot(t))
	for _, c := range []struct {
		args []string
		exit int
		out  string
	}{
		{nil, 1, ""},
		{[]string{"--help"}, 0, "usage: irl"},
		{[]string{"sopt"}, 1, ""},
		{[]string{"msc"}, 1, ""},
		{[]string{"nope"}, 1, ""},
		{[]string{"capabilities", "--pretty"}, 0, `"schema": "ir-lean.irl.capabilities/1"`},
		{[]string{"mcp", "extra"}, 1, ""},
	} {
		var stdout, stderr strings.Builder
		if got := run(c.args, strings.NewReader(""), &stdout, &stderr); got != c.exit {
			t.Errorf("irl %v exited %d, not %d: %s", c.args, got, c.exit, stderr.String())
		}
		if !strings.Contains(stdout.String(), c.out) {
			t.Errorf("irl %v printed %q", c.args, stdout.String())
		}
	}
	t.Setenv("IRL_ROOT", t.TempDir())
	var stderr strings.Builder
	if run([]string{"verify"}, nil, io.Discard, &stderr) != 1 || !strings.Contains(stderr.String(), "isn't an ir-lean checkout") {
		t.Errorf("a wrong IRL_ROOT gave %q", stderr.String())
	}
}

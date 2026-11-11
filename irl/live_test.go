package main

import (
	"encoding/json"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"syscall"
	"testing"
	"time"
)

// These run the built irl against the real tools, with Lean, as the irl_live test does: after
// `cmake --build build` and `lake build`, with IRL_LIVE=1, and IRL_BIN if irl isn't build/irl.

func live(t *testing.T) (root, bin string) {
	t.Helper()
	if os.Getenv("IRL_LIVE") == "" {
		t.Skip("set IRL_LIVE=1, after building irl, the emitter and IRLean, to run irl against the real tools")
	}
	root = realRoot(t)
	bin = os.Getenv("IRL_BIN")
	if bin == "" {
		bin = filepath.Join(root, "build", "irl")
	}
	return root, bin
}

// cli runs irl from the checkout's root and reads the JSON it prints, whatever it exits with.
func cli(t *testing.T, bin, root string, args ...string) map[string]any {
	t.Helper()
	cmd := exec.Command(bin, args...)
	cmd.Dir = root
	out, err := cmd.Output()
	if _, exited := errors.AsType[*exec.ExitError](err); err != nil && !exited {
		t.Fatal(err)
	}
	var answer map[string]any
	if err := json.Unmarshal(out, &answer); err != nil {
		t.Fatalf("irl %v printed %q: %v", args, out, err)
	}
	return answer
}

// mcp starts `irl mcp` in the checkout's root, and initializes a session with it.
func mcp(t *testing.T, bin, root string) (*session, *exec.Cmd) {
	t.Helper()
	cmd := exec.Command(bin, "mcp")
	cmd.Dir = root
	cmd.Stderr = os.Stderr
	in, err := cmd.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}
	out, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		in.Close()
		if err := cmd.Wait(); err != nil {
			t.Errorf("irl mcp: %v", err)
		}
	})
	s := newSession(t, in, out)
	s.request(0, "initialize", map[string]any{"protocolVersion": protocolVersions[0]})
	s.send(map[string]any{"jsonrpc": "2.0", "method": "notifications/initialized"})
	return s, cmd
}

// sameDecision fails unless both answers decided the same: the fields named, as each tool's contract defines
// them. Timings and run directories differ from run to run.
func sameDecision(t *testing.T, what string, a, b map[string]any, fields ...string) {
	t.Helper()
	for _, f := range fields {
		x, y := must(json.Marshal(a[f])), must(json.Marshal(b[f]))
		if string(x) != string(y) {
			t.Errorf("%s: the command line says %s is %s, and MCP %s", what, f, x, y)
		}
	}
}

func TestLiveVerifyAnswersTheSameBothWays(t *testing.T) {
	root, bin := live(t)
	s, _ := mcp(t, bin, root)
	statement := "∀ x : BitVec 32, Real.popcount (some x) = IRLean.Outcome.ok (some (x &&& 1#32))"
	for _, c := range []struct {
		what  string
		flags []string
		args  map[string]any
		want  string
	}{
		{
			"a wrong statement",
			[]string{"--statement", statement, "--witness", `{"x": "3#32"}`},
			map[string]any{"statement": statement, "witnesses": []map[string]string{{"x": "3#32"}}},
			"counterexample",
		},
		{
			"popcount's proof",
			[]string{"--proof", "tests/proofs/Popcount.lean", "--theorem", "popcount_correct"},
			map[string]any{"proof": "tests/proofs/Popcount.lean", "theorem": "popcount_correct"},
			"proved",
		},
	} {
		flags := append([]string{"verify", "check", "--c", "tests/real/bi_reverse.c", "--namespace", "Real",
			"--function", "popcount"}, c.flags...)
		byCLI := cli(t, bin, root, flags...)
		arguments := map[string]any{"input": map[string]any{"c": "tests/real/bi_reverse.c"}, "namespace": "Real",
			"function": "popcount"}
		for k, v := range c.args {
			arguments[k] = v
		}
		r := s.call(c.what, "verify_check", arguments)
		byMCP := r["structuredContent"].(map[string]any)
		if byCLI["status"] != c.want || r["isError"] != false {
			t.Errorf("%s: the command line says %v, and MCP %v", c.what, byCLI["status"], r)
		}
		sameDecision(t, c.what, byCLI, byMCP, "schema", "status", "reason", "exit_code", "claim", "counterexample",
			"assumptions")
	}
}

func TestLivePtfAnswersTheSameBothWays(t *testing.T) {
	root, bin := live(t)
	s, _ := mcp(t, bin, root)
	statement := "∀ (x : BitVec 32), Cases.low16 (some x) = IRLean.Outcome.ok (some x)"
	byCLI := cli(t, bin, root, "ptf", "run", "--ir", "tests/prooftest/Cases.ll", "--namespace", "Cases",
		"--function", "low16", "--statement", statement, "--no-store")
	r := s.call(1, "ptf_run", map[string]any{"input": map[string]any{"ir": "tests/prooftest/Cases.ll"},
		"namespace": "Cases", "function": "low16", "statement": statement, "store": nil})
	byMCP := r["structuredContent"].(map[string]any)
	if byCLI["status"] != "counterexample" || r["isError"] != false {
		t.Errorf("the command line says %v, and MCP %v", byCLI["status"], r)
	}
	sameDecision(t, "low16", byCLI, byMCP, "schema", "tier", "status", "reason", "exit_code", "proved")
	sameDecision(t, "low16's counterexample", byCLI["counterexample"].(map[string]any),
		byMCP["counterexample"].(map[string]any), "assignment", "instance", "evidence")
}

// descendants is every process under pid, by name, from ps, which Linux and macOS both have.
func descendants(t *testing.T, pid int) map[int]string {
	t.Helper()
	out, err := exec.Command("ps", "-eo", "pid=,ppid=,comm=").Output()
	if err != nil {
		t.Fatal(err)
	}
	children, names := map[int][]int{}, map[int]string{}
	for line := range strings.Lines(string(out)) {
		f := strings.Fields(line)
		if len(f) < 3 {
			continue
		}
		p, _ := strconv.Atoi(f[0])
		parent, _ := strconv.Atoi(f[1])
		children[parent] = append(children[parent], p)
		names[p] = filepath.Base(f[2])
	}
	found := map[int]string{}
	for stack := slices.Clone(children[pid]); len(stack) > 0; {
		p := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		found[p] = names[p]
		stack = append(stack, children[p]...)
	}
	return found
}

// A cancelled call leaves nothing running: not the tool, and not the Lean it started in a session of its own,
// which irl's signal to the tool's process group doesn't reach. The proof checked is popcount's, made to take two
// minutes, so Lean stopping within seconds of the cancel is the cancel's doing, not the proof finishing. If irl
// sent the tool SIGKILL, Python couldn't stop Lean, and this fails.
func TestLiveCancellingStopsLean(t *testing.T) {
	root, bin := live(t)
	proof := string(must(os.ReadFile(filepath.Join(root, "tests", "proofs", "Popcount.lean"))))
	statement := "    popcount (some x) = Outcome.ok (some (pop x)) := by\n"
	if strings.Count(proof, statement) != 1 {
		t.Fatalf("tests/proofs/Popcount.lean doesn't have popcount_correct's statement as this test expects")
	}
	slow := filepath.Join(t.TempDir(), "Popcount.lean")
	if err := os.WriteFile(slow, []byte(strings.Replace(proof, statement, statement+"  sleep 120000\n", 1)), 0o644); err != nil {
		t.Fatal(err)
	}
	s, server := mcp(t, bin, root)
	s.send(map[string]any{"jsonrpc": "2.0", "id": "slow", "method": "tools/call", "params": map[string]any{
		"name": "verify_check",
		"arguments": map[string]any{"input": map[string]any{"c": "tests/real/bi_reverse.c"}, "namespace": "Real",
			"function": "popcount", "proof": slow, "theorem": "popcount_correct"},
	}})
	// verify runs Lean briefly as it sets up, to read its version, and each of those ends by itself. The one to
	// cancel is checking the proof: a Lean process still running a second after it was first seen.
	var running map[int]string
	seen := map[int]time.Time{}
	for start := time.Now(); ; time.Sleep(50 * time.Millisecond) {
		running = descendants(t, server.Process.Pid)
		checking := false
		for pid, name := range running {
			if name != "lean" {
				continue
			}
			if _, ok := seen[pid]; !ok {
				seen[pid] = time.Now()
			}
			checking = checking || time.Since(seen[pid]) >= time.Second
		}
		if checking {
			break
		}
		if time.Since(start) > time.Minute {
			t.Fatalf("no Lean process ran for a second: %v", running)
		}
	}
	s.send(map[string]any{"jsonrpc": "2.0", "method": "notifications/cancelled",
		"params": map[string]any{"requestId": "slow"}})
	deadline := time.Now().Add(5 * time.Second)
	for pid, name := range running {
		for syscall.Kill(pid, 0) == nil {
			if time.Now().After(deadline) {
				t.Fatalf("%s, pid %d, is still running after the call was cancelled", name, pid)
			}
			time.Sleep(50 * time.Millisecond)
		}
	}
	// The cancelled call got no response: the next message is the ping's.
	if m := s.request("after", "ping", nil); m["error"] != nil {
		t.Errorf("ping gave %v", m)
	}
}

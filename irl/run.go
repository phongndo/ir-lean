package main

import (
	"bytes"
	"context"
	"os/exec"
	"syscall"
	"time"
)

// ran is what running one tool gave: what it printed, how it exited, and whether it was cancelled.
type ran struct {
	stdout []byte
	stderr []byte
	// The exit code, or -1 if it didn't start or a signal ended it.
	exit int
	// Why it didn't start, if it didn't.
	err       error
	cancelled bool
}

// runTool runs argv in dir, with stdin on its standard input, until it exits or ctx is done.
//
// The tool runs in a process group of its own. When ctx is done, irl sends the group SIGINT, and after
// grace, SIGKILL. The Python tools run Lean in sessions of their own, which the group doesn't reach, and
// SIGINT is what makes them stop it: Python raises KeyboardInterrupt, and irlean.proc.run kills everything
// the command started before it returns. SIGKILL would leave those running.
func runTool(ctx context.Context, dir string, argv []string, stdin []byte, grace time.Duration) ran {
	cmd := exec.Command(argv[0], argv[1:]...)
	cmd.Dir = dir
	if stdin != nil {
		cmd.Stdin = bytes.NewReader(stdin)
	}
	var stdout bytes.Buffer
	stderr := &tail{max: 64 << 10}
	cmd.Stdout, cmd.Stderr = &stdout, stderr
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	// Something the tool started may keep its output open after it exits. Its answer is in by then.
	cmd.WaitDelay = 5 * time.Second
	if err := cmd.Start(); err != nil {
		return ran{exit: -1, err: err}
	}
	done := make(chan struct{})
	go func() {
		_ = cmd.Wait()
		close(done)
	}()
	cancelled := false
	select {
	case <-done:
	case <-ctx.Done():
		cancelled = true
		group := -cmd.Process.Pid
		_ = syscall.Kill(group, syscall.SIGINT)
		select {
		case <-done:
		case <-time.After(grace):
			_ = syscall.Kill(group, syscall.SIGKILL)
			<-done
		}
	}
	return ran{stdout: stdout.Bytes(), stderr: stderr.bytes(), exit: cmd.ProcessState.ExitCode(), cancelled: cancelled}
}

// tail keeps the last max bytes written to it, so a tool that prints a lot can't fill irl's memory.
type tail struct {
	buf []byte
	max int
}

func (t *tail) Write(p []byte) (int, error) {
	t.buf = append(t.buf, p...)
	if len(t.buf) > t.max {
		t.buf = append(t.buf[:0:0], t.buf[len(t.buf)-t.max:]...)
	}
	return len(p), nil
}

func (t *tail) bytes() []byte { return t.buf }

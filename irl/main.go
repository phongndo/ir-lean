// Command irl is ir-lean's command line, and its MCP server for agents.
//
// Each command is one of the repo's tools: the emitter, in C++, and verify, ptf and store, in Python, which
// run Lean and decide what it showed. irl decides nothing itself. A command is the tool, run in irl's place,
// and an MCP call's result is the JSON the tool printed. docs/irl.md says what each answers.
package main

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"text/tabwriter"
)

// usage lists the commands from commands and planned, so it can't name one that isn't there.
func usage() string {
	var b strings.Builder
	b.WriteString("usage: irl COMMAND [ARGUMENTS]\n\nEach command runs one of the tools in the ir-lean checkout irl belongs to:\n\n")
	// The last cell of a line isn't part of a column, so nothing pads it. Both lists share the first column's
	// width: two spaces, capabilities, and two more.
	w := tabwriter.NewWriter(&b, 16, 0, 2, ' ', 0)
	for _, c := range commands {
		fmt.Fprintf(w, "  %s\t%s\t%s\n", c.name, c.what, c.path)
	}
	fmt.Fprintf(w, "  capabilities\tevery command's contract, and which are built, as JSON [--pretty]\n")
	fmt.Fprintf(w, "  mcp\tserve verify, ptf and store to an agent, over MCP on stdio\n")
	_ = w.Flush()
	b.WriteString("\nNamed, and not built yet:\n\n")
	w = tabwriter.NewWriter(&b, 16, 0, 2, ' ', 0)
	for _, c := range planned {
		fmt.Fprintf(w, "  %s\t%s\n", c.name, c.what)
	}
	_ = w.Flush()
	b.WriteString("\n\"irl COMMAND --help\" says what a command takes. IRL_ROOT names the checkout, if irl can't " +
		"find it.\nirl mcp runs as many calls that use Lean at once as IRL_JOBS says, or else LEAN_JOBS, or else 2.\n" +
		"docs/irl.md has the rest.\n")
	return b.String()
}

func main() {
	os.Exit(run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr))
}

// run runs a command and returns its exit code. A command that's a tool replaces irl with it, and doesn't
// return. irl's own errors exit 1, never 2, which a tool's answer uses for a counterexample.
func run(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		fmt.Fprint(stderr, usage())
		return 1
	}
	if args[0] == "-h" || args[0] == "--help" || args[0] == "help" {
		fmt.Fprint(stdout, usage())
		return 0
	}
	root, err := findRoot()
	if err != nil {
		fmt.Fprintf(stderr, "irl: %v\n", err)
		return 1
	}
	name, rest := args[0], args[1:]
	if c, ok := findCommand(commands, name); ok {
		return execTool(root, c, rest, stderr)
	}
	if c, ok := findCommand(planned, name); ok {
		fmt.Fprintf(stderr, "irl: %s, %s, isn't built yet. docs/roadmap.md says where it stands\n", c.name, c.what)
		return 1
	}
	switch name {
	case "capabilities":
		return printCapabilities(root, rest, stdout, stderr)
	case "mcp":
		return serveMCP(root, rest, stdin, stdout, stderr)
	}
	fmt.Fprintf(stderr, "irl: no command %q\n\n%s", name, usage())
	return 1
}

// execTool replaces irl with the tool, so it has irl's arguments, terminal, signals and exit code, and irl
// costs nothing once it has started.
func execTool(root string, c command, args []string, stderr io.Writer) int {
	path := filepath.Join(root, c.path)
	if _, err := os.Stat(path); err != nil {
		fmt.Fprintf(stderr, "irl: %s isn't built: %v. docs/irl.md says how to build it\n", c.path, err)
		return 1
	}
	err := syscall.Exec(path, append([]string{path}, args...), os.Environ())
	fmt.Fprintf(stderr, "irl: can't run %s: %v\n", c.path, err)
	return 1
}

func printCapabilities(root string, args []string, stdout, stderr io.Writer) int {
	pretty := len(args) == 1 && args[0] == "--pretty"
	if len(args) > 0 && !pretty {
		fmt.Fprintln(stderr, "usage: irl capabilities [--pretty]")
		return 1
	}
	caps, err := capabilities(context.Background(), root)
	var text []byte
	if pretty {
		text, _ = json.MarshalIndent(caps, "", "  ")
	} else {
		text, _ = json.Marshal(caps)
	}
	fmt.Fprintf(stdout, "%s\n", text)
	if err != nil {
		fmt.Fprintf(stderr, "irl: %v\n", err)
		return 1
	}
	return 0
}

// serveMCP serves until stdin closes or a signal comes, then stops every call still running.
func serveMCP(root string, args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) > 0 {
		fmt.Fprintln(stderr, "usage: irl mcp")
		return 1
	}
	base, err := os.Getwd()
	if err != nil {
		fmt.Fprintf(stderr, "irl mcp: %v\n", err)
		return 1
	}
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	s, err := newServer(ctx, root, base, jobs(), stdout)
	if err != nil {
		fmt.Fprintf(stderr, "irl mcp: can't read the tools' contracts: %v\n", err)
		return 1
	}
	fmt.Fprintf(stderr, "irl mcp: %d tools from %s, up to %d calls using Lean at once\n", len(s.tools), root,
		cap(s.slots))
	if err := s.serve(ctx, stdin); err != nil {
		fmt.Fprintf(stderr, "irl mcp: %v\n", err)
		return 1
	}
	return 0
}

// jobs is how many calls that run Lean may run at once. The dev shell sets LEAN_JOBS to how many Lean
// processes fit in the machine's memory.
func jobs() int {
	for _, name := range []string{"IRL_JOBS", "LEAN_JOBS"} {
		if n, err := strconv.Atoi(os.Getenv(name)); err == nil && n > 0 {
			return n
		}
	}
	return 2
}

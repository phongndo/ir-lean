# irl

`irl` is ir-lean's command line, and the MCP server agents use. Every command is one of the repo's tools, and irl
decides nothing itself: what a tool answers is what irl answers. For what any answer means, see [trust](trust.md).

Facts here were checked on 2026-11-10, on z, x86-64 Linux with 32 cores, on top of `60df346`, with Go 1.26.10, Lean
4.35.0 and clang 23.1.3, in the dev shell.

## The commands

`cmake --build build` builds `build/irl`, with the emitter. Each command runs a tool in irl's place, with irl's
arguments, terminal, signals and exit code:

| Command | Runs | What it does |
| --- | --- | --- |
| `irl emit` | `build/ir-lean` | Translates LLVM IR to Lean ([design](design.md)) |
| `irl verify` | `tools/verify.py` | Checks one claim about one function ([verify](verify.md)) |
| `irl ptf` | `tools/prooftest/prooftest.py` | Proof tests: runs a property on generated inputs ([proof tests](proof-tests.md)) |
| `irl store` | `tools/store/store.py` | Finds, checks and adds stored lemmas ([lemma store](lemma-store.md)) |
| `irl capabilities` | Each tool's `capabilities` | Every command's contract, and which commands are built, as JSON |
| `irl mcp` | The tools above | Serves them to an agent, over MCP |

Two more have names and nothing built yet: `irl sopt`, the superoptimizer, and `irl msc`, the memory-safety checker.
Each says so and exits 1. [The roadmap](roadmap.md#names-and-languages-decided-on-2026-11-10) has where the names come
from.

```console
$ build/irl verify check --c tests/real/bi_reverse.c --namespace Real --function popcount \
    --proof tests/proofs/Popcount.lean --theorem popcount_correct --pretty
```

That's [verify's example](verify.md#an-example), and prints what `tools/verify.py` prints. irl finds the checkout
from its own binary, so `build/irl` works from any directory, and `IRL_ROOT` names another. Its own errors, such as
an unknown command, exit 1, never 2, which `verify` and `ptf` use for a counterexample.

irl costs nothing once a tool starts: it replaces itself with the tool. Starting Python and its imports takes 30 to
36 ms for each of `verify`, `ptf` and `store`, against about 2.1 s for a check, and `irl capabilities` reads all
three contracts at once in about 60 ms.

## The MCP server

`irl mcp` serves four tools over MCP's stdio transport, one JSON-RPC message a line. To add it to Claude Code, from
the checkout:

```sh
claude mcp add irl -- nix develop "$PWD" -c "$PWD/build/irl" mcp
```

It runs the tools, so it needs the dev shell's clang, Lean and Python, which `nix develop` gives it. In a session
already in the shell, `claude mcp add irl -- "$PWD/build/irl" mcp` does too. A path in a request is absolute, or
relative to the directory the server started in, which is the agent's.

| Tool | Runs | Takes | Answers |
| --- | --- | --- | --- |
| `verify_check` | `irl verify check -` | verify's request | `ir-lean.verify/1` |
| `ptf_run` | `irl ptf run -` | ptf's request | `ir-lean.prooftest/1` |
| `store_lookup` | `irl store lookup --json` | `statement`, and the `imports` it needs | `ir-lean.store.lookup/1` |
| `capabilities` | `irl capabilities` | Nothing | `ir-lean.irl.capabilities/1` |

### What a call answers

- **The tool's answer, unchanged.** A call's arguments are the tool's request, sent on stdin, and the result's text
  is the JSON the tool printed, byte for byte, with the same JSON as its structured content. Each input schema is
  the tool's own `request_json_schema`, from its `capabilities`, and each output schema says which schema and
  statuses it answers with. The tool still decides whether a request is valid, as it does for a request file.
- **An error is only a failed request or tool.** `isError` is true when the answer's status is `error`, its reason
  `invalid_request` or `internal_error`, or the tool printed no JSON. A counterexample, `unsupported`, `timeout` or
  `unknown` is an answer, and only `proved` says a claim holds. The server's instructions say so to the agent.
- **It never calls a model,** as [decision 5 after #103](roadmap.md#thirteen-decisions-of-2026-11-09-after-103)
  requires of every tool that ships.
- **Every answer reproduces from a terminal.** A verify answer's `reproduce.command` reruns it, and the same request
  is `irl verify check request.json`.

### Running and stopping

- **Calls that run Lean wait for a slot.** `verify_check`, `ptf_run` and `store_lookup` run Lean, and as many run at
  once as `IRL_JOBS` says, or else `LEAN_JOBS`, which the dev shell sets to how many Lean processes fit in memory,
  or else 2. The others wait. The slots are the server's own: two agents, each with a server, don't share them, and
  `verify` and `ptf` don't take a slot in the machine's [pool of heavy jobs](corpus.md#measuring-a-heavy-job).
- **Cancelling stops everything a call started.** On `notifications/cancelled`, on stdin closing, or on SIGINT or
  SIGTERM to the server, irl sends the tool's process group SIGINT. Python raises `KeyboardInterrupt`, and
  `irlean.proc` kills what it started, Lean included, though Lean runs in a session of its own. After 10 s irl sends
  SIGKILL. A cancelled call gets no response, as MCP says.
- **A long call reports progress.** A call with a `progressToken` gets `notifications/progress` every 15 s, with how
  long it has run and whether it's still waiting for a slot.

### What it speaks

MCP 2025-11-25, 2025-06-18, 2025-03-26 and 2024-11-05: it answers a client with the version it asks for, or the
newest. It serves tools only: no resources, prompts or sampling, and the list of tools doesn't change.

It's Go with only its standard library, as [the decision](roadmap.md#names-and-languages-decided-on-2026-11-10) has
it. The dev shell's Go builds it, and nothing is downloaded.

## What it doesn't do yet

- **`emit` isn't an MCP tool.** It prints Lean, not a JSON answer, and `verify_check` already says when the emitter
  refuses a function, with the emitter's reason, as `unsupported`.
- **The store's other commands aren't MCP tools.** `store_add` comes with sopt's proposer, which is what will add
  rules.
- **It isn't packaged.** `build/irl` needs its checkout, built, and the dev shell. A flake app that carries the
  toolchain is open.
- **Lean starts again for each call.** Starting it is most of a short check's time. Keeping it loaded between calls,
  and caching answers by what they were asked, are the speed work that's open for irl.

## Tests

`irl` checks the server and the command line against stub tools, with no Lean, in about 3 s, and `irl_live` checks
`build/irl` against the real tools, with Lean, in about 20 s. [Testing](testing.md) says what each checks.
`tests/lint.sh` runs `gofmt` and `go vet` on irl, and `tests/lsp.py` starts `gopls` on it.

# Process

How a change goes from an idea to `main`: a design reviewed before any code, one full review, fixes that close a
kind of bug instead of one instance of it, and a stop rule. [Bug classes](bug-classes.md) is the ledger this reads
from and adds to. Facts here were checked on 2026-11-10, at `f140938`.

## Why it changed

On 2026-11-10, five pull requests took 3 to 5 rounds of review each. They were
[#109](https://github.com/phongndo/ir-lean/pull/109), [#110](https://github.com/phongndo/ir-lean/pull/110),
[#115](https://github.com/phongndo/ir-lean/pull/115), [#116](https://github.com/phongndo/ir-lean/pull/116) and
[#117](https://github.com/phongndo/ir-lean/pull/117), whose round 3 was its last. Every blocker or should that rounds
2 and later raised in them, as each pull request's Review section records it, was traced to where it came from. A
finding a later round reported again as still open counts each time; one a round only pointed at others through
counts once:

| Pull request | Rounds | Raised in round 2 or later | A fix that didn't close it | In code a fix wrote | In the code reviewed first |
| --- | ---: | ---: | ---: | ---: | ---: |
| #109, the rule search | 5 | 9 | 4 | 4 | 1 |
| #110, source annotations | 4 | 2 | 0 | 2 | 0 |
| #115, F4 on SIMD | 4 | 4 | 3 | 1 | 0 |
| #116, the corpus fixed | 4 | 6 | 2 | 4 | 0 |
| #117, harness and board | 3 | 7 | 3 | 4 | 0 |
| **All** | | **28** | **12** | **15** | **1** |

Round 1 found the real problems. After it, 27 of the 28 findings were about the fixes. 12 times a fix closed the
case it was shown and left its siblings open: `{repo}` was refused, then `env -C {repo}`, then `{repo}/`. 15 times a
fix added something new, such as a seal, a stamp, a reservation or a dry run of `make`, and the next round found the
bug in that. One class, a limit or a failure counted as a pass, was fixed locally in six pull requests and came back
each time.

So a review here doesn't hunt for the next layer after round 1, and a fix closes a class, not an instance.

## The steps

### 0. The design, before any code

A change starts as one page in its pull request's description, or in a doc it adds, and the reviewer approves it
before any code is written. It says:

- **The claim.** What a positive answer means, exactly: proved, certified, passed, a win, and what evidence each needs.
- **What it holds against, and what it doesn't.** In scope as a rule: tool bugs, crashes, limits, model stops,
  mistakes by whoever runs it, and other processes in the same checkout. Out of scope as a rule: code running as the
  same user that changes files on purpose, as [the gates' promise](rules.md#what-the-gates-promise) says.
- **The invariants, as the tests that will check them.** Written first.
- **What it reuses.** Which [bug classes](bug-classes.md) it touches, and the guard each has. A change adds no new
  place that decides a verdict, and doesn't read another tool's text output when a structured form or LLVM's API
  exists.
- **Its size.** At most about 1,500 lines of changed code. Bigger work is split along its seams into pull requests
  that each leave everything working.

A design takes one review. A problem of a whole kind is cheap to see when it's one sentence, and expensive once it's
a thousand lines.

### 1. Build it

Tests for the invariants first, then the code. Work that depends on another change waits for that change to merge:
two lanes don't build on the same thing at once, and adapting to a change that landed underneath is its own reviewed
change, never part of a merge commit.

### 2. Review, once, in full

An independent reviewer, a model other than the author's, at its highest effort, reads the whole change with the
design and [bug classes](bug-classes.md) beside it. A finding outside what the design holds against is deferred: it
goes to the follow-ups, not into the loop.

### 3. Triage, before fixing

Whoever runs the change, not the one fixing it, sorts each finding first:

- **Name its class** in one line: a check then a use, a text form a pattern misses, a reader that skips validation, a
  limit counted as a pass. If it's in [the ledger](bug-classes.md), it's that class.
- **Find its siblings**: every other place in the change with the same shape.
- **Choose the fix, best first**: make it impossible (a private directory, a structured field instead of a string,
  one loader, default-deny), then one guard every case goes through, and an instance fix only for a true one-off.
- **Test the class, not the case shown**: for example, every evidence state that isn't clean, not the one exit code
  the reviewer tried.

### 4. A budget, and a stop

- A fix that adds a mechanism, a new module, file format, record or check of its own, is a design change. So is one
  bigger than 30% of the change review 1 read, counting added and removed lines of code and tests, not docs, as
  `git diff --shortstat` does: the fix's commits, against the base to the head review 1 read. That piece goes back
  to step 0 as a change of its own, or out.
- **Two strikes.** If the second review finds a class still open, or a new blocker in code the fix wrote, the fixing
  stops. That piece is designed again as a change of its own, or cut from this one. There's no third round of
  patches.

### 5. Review the fix, for closure

The second review reads only the fix, and answers one question for each finding: does this close the class? It lists
any sibling still open. It doesn't look for new ground. Anything new it sees anyway is deferred unless it's a blocker,
and a new blocker is a strike.

A change merges when the reviewer approves the current head, every check passes on it, and nothing blocking is open.
Blocking are review 1's blockers and shoulds, and any blocker. Deferred findings don't block: the description lists
each, with its class, as a follow-up. The description ends with how many rounds the change took, its findings by
class, and how many were in code a fix wrote. The aim is two rounds at most, and none in a fix's code.

## Across pull requests

- **A class seen twice gets one guard.** The second time a [bug class](bug-classes.md) shows up, its central guard,
  and the test that enforces it, comes before any more feature work that could repeat it.
- **Foundations first.** Work that changes what others build on merges before what builds on it.
- **One claim a pull request.** A change that proves something and one that measures something are two changes.

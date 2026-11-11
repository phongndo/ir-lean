"""The benchmark protocol's statistic, and the rule a candidate is read by: docs/kernels.md's "The benchmark
protocol", "Measurably faster" and "What a win is". Pure functions, with no process, file or clock in them, so
the rule can be checked on numbers alone, as tests/kernels_bench_test.py does.

A pair is a baseline run and a candidate run, back to back. Its ratio is baseline time over candidate time,
or, where the measure is a rate, candidate rate over baseline rate, so that above 1 is faster either way. The
statistic is the median of the ratios, with a 95% percentile bootstrap interval from 20,000 resamples of the
pairs, as tests/llama/measure.py computes it for the Q5 rewrite: the 500th and 19,500th of the sorted medians.

Measurably faster, decision 5 of the kernel corpus, needs all of:

1. at least 30 pairs, in at least 2 confirmation sessions;
2. the pooled interval's lower end at or above 1.005;
3. every session's median above 1;
4. no other workload of the project slower: each one's pooled interval reaches 1 or above.

The rule doesn't say when a candidate is slower, only that the board says so. Here it's the mirror of the
first three: at least 30 pairs in at least 2 confirmation sessions, the pooled interval's upper end at or
below 1 / 1.005, and every session's median below 1. Anything else is inconclusive.
"""

from __future__ import annotations

import random
import statistics
from collections.abc import Sequence
from dataclasses import asdict, dataclass
from typing import Any

# The two kinds of measure a workload has: the wall time of its command, or a rate the benchmark prints.
TIME = "time"
RATE = "rate"
MEASURES = (TIME, RATE)
# A session that picks among candidates is exploratory; only confirmation sessions count.
EXPLORATORY = "exploratory"
CONFIRMATION = "confirmation"
KINDS = (EXPLORATORY, CONFIRMATION)
# What a comparison comes to.
FASTER = "faster"
SLOWER = "slower"
INCONCLUSIVE = "inconclusive"


@dataclass(frozen=True)
class Rule:
    """What a comparison is read by. The defaults are the protocol's and decision 5's, and only a comparison
    made with them can put a win on the board. tests/kernels_bench_test.py lowers `min_seconds` alone, so its
    tiny workload runs in seconds, and checks the board refuses what that gives."""

    min_pairs: int = 30
    min_sessions: int = 2
    threshold: float = 1.005
    resamples: int = 20000
    confidence: float = 0.95
    # A run shorter than this is repeated inside one timed command until it isn't.
    min_seconds: float = 2.0

    def as_record(self) -> dict[str, Any]:
        return asdict(self)


PROTOCOL = Rule()


def ratio(baseline: float, candidate: float, measure: str) -> float:
    """A pair's ratio, above 1 when the candidate is faster."""
    if measure not in MEASURES:
        raise ValueError(f"measure {measure!r} isn't one of {', '.join(MEASURES)}")
    if baseline <= 0 or candidate <= 0:
        raise ValueError(f"a time or a rate is positive, not {baseline} and {candidate}")
    return baseline / candidate if measure == TIME else candidate / baseline


def interval(ratios: Sequence[float], seed: int, rule: Rule = PROTOCOL) -> tuple[float, float]:
    """The percentile bootstrap interval of the median of `ratios`: `rule.resamples` resamples of the pairs,
    with replacement, from `random.Random(seed)`, so the same seed gives the same interval."""
    if not ratios:
        raise ValueError("no pairs")
    rng = random.Random(seed)
    n = len(ratios)
    medians = sorted(statistics.median(rng.choices(ratios, k=n)) for _ in range(rule.resamples))
    tail = (1 - rule.confidence) / 2
    # For 20,000 resamples, the 500th and the 19,500th, as tests/llama/measure.py takes them.
    low = round(rule.resamples * tail) - 1
    high = round(rule.resamples * (1 - tail)) - 1
    return medians[low], medians[high]


def summary(ratios: Sequence[float], seed: int, rule: Rule = PROTOCOL) -> dict[str, Any]:
    """The statistic over some pairs: how many, their median, its interval, and the range."""
    low, high = interval(ratios, seed, rule)
    return {
        "pairs": len(ratios),
        "median": statistics.median(ratios),
        "interval": [low, high],
        "bootstrap_seed": seed,
        "resamples": rule.resamples,
        "range": [min(ratios), max(ratios)],
        "faster_pairs": sum(r > 1 for r in ratios),
    }


def verdict(
    sessions: Sequence[Sequence[float]],
    kinds: Sequence[str],
    seed: int,
    others: dict[str, list[float] | None] | None = None,
    rule: Rule = PROTOCOL,
) -> dict[str, Any]:
    """Reads `sessions`, each a list of paired ratios on one workload, by the rule. `kinds` says what kind
    each session is. `others` gives each of the project's other workloads the pooled interval measured on
    it, or None where it wasn't measured: condition 4 holds only when every one reaches 1. Returns the
    verdict, each condition and whether it held, and the statistic, per session and pooled."""
    if len(sessions) != len(kinds) or not sessions:
        raise ValueError("one kind for each session, and at least one session")
    if any(k not in KINDS for k in kinds):
        raise ValueError(f"a session is one of {', '.join(KINDS)}")
    per = [summary(s, seed + n, rule) for n, s in enumerate(sessions, 1)]
    pooled = summary([r for s in sessions for r in s], seed, rule)
    confirmation = all(k == CONFIRMATION for k in kinds)
    enough = pooled["pairs"] >= rule.min_pairs and len(sessions) >= rule.min_sessions
    others = others or {}
    unmeasured = sorted(w for w, i in others.items() if i is None)
    ends = {w: i[1] for w, i in others.items() if i is not None}
    below = sorted(w for w, end in ends.items() if end < 1)
    conditions = {
        "confirmation": {
            "held": confirmation,
            "says": "only confirmation sessions count",
        },
        "pairs": {
            "held": enough,
            "says": f"at least {rule.min_pairs} pairs in at least {rule.min_sessions} sessions: "
            f"{pooled['pairs']} in {len(sessions)}",
        },
        "interval": {
            "held": pooled["interval"][0] >= rule.threshold,
            "says": f"the pooled interval's lower end at or above {rule.threshold}: "
            f"{pooled['interval'][0]:.4f}",
        },
        "sessions": {
            "held": all(s["median"] > 1 for s in per),
            "says": "every session's median above 1: " + ", ".join(f"{s['median']:.4f}" for s in per),
        },
        "others": {
            "held": not unmeasured and not below,
            "says": "no other workload slower: "
            + (
                "; ".join(
                    [f"{w} wasn't measured" for w in unmeasured]
                    + [f"{w}'s interval ends at {ends[w]:.4f}" for w in below]
                )
                or (
                    f"each of {', '.join(sorted(others))} reaches 1" if others else "it has no other workload"
                )
            ),
        },
    }
    slower = (
        confirmation
        and enough
        and pooled["interval"][1] <= 1 / rule.threshold
        and all(s["median"] < 1 for s in per)
    )
    if all(c["held"] for c in conditions.values()):
        outcome = FASTER
    elif slower:
        outcome = SLOWER
    else:
        outcome = INCONCLUSIVE
    return {
        "verdict": outcome,
        "conditions": conditions,
        "sessions": per,
        "pooled": pooled,
        "rule": rule.as_record(),
    }

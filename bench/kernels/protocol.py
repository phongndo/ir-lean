"""The benchmark protocol's statistic, and the conditions a candidate is read by: docs/kernels.md's "The
benchmark protocol" and "Measurably faster". Pure functions, with no process, file or clock in them, so the
rule can be checked on numbers alone, as tests/timing_test.py does.

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
below 1 / 1.005, and every session's median below 1.

Nor does it say how a workload that measures several figures combines them, as `xxhsum -b` gives one for each
of four hashes. `conditions` is its strictest reading: a condition holds only if it holds for every figure,
so that one figure can't hide another.

This says which conditions hold. It doesn't say what they come to: that's irlean.verdict's, which
bench/kernels/timing.py asks.
"""

from __future__ import annotations

import random
import statistics
from collections.abc import Mapping, Sequence
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


def conditions(
    figures: Mapping[str, Sequence[Sequence[float]]],
    kinds: Sequence[str],
    seed: int,
    others: dict[str, list[float] | None] | None = None,
    rule: Rule = PROTOCOL,
) -> dict[str, Any]:
    """Which of the rule's conditions hold of `figures`: each figure's sessions of paired ratios on one
    workload, with what kind each session is. `others` gives each of the project's other workloads the
    pooled interval measured on it, or None where it wasn't measured. Returns each condition, whether it held
    for every figure, and what was found, with the statistic of each figure, per session and pooled.
    `interval_above` and `sessions_above` are the rule's second and third, and `interval_below` and
    `sessions_below` their mirror."""
    if not figures or any(len(s) != len(kinds) or not s for s in figures.values()):
        raise ValueError("at least one figure, and one kind for each of its sessions")
    if any(k not in KINDS for k in kinds):
        raise ValueError(f"a session is one of {', '.join(KINDS)}")
    stats: dict[str, dict[str, Any]] = {}
    for name, sessions in sorted(figures.items()):
        stats[name] = {
            "sessions": [summary(s, seed + n, rule) for n, s in enumerate(sessions, 1)],
            "pooled": summary([r for s in sessions for r in s], seed, rule),
        }
    pairs = min(s["pooled"]["pairs"] for s in stats.values())
    low = min(s["pooled"]["interval"][0] for s in stats.values())
    high = max(s["pooled"]["interval"][1] for s in stats.values())
    medians = [m["median"] for s in stats.values() for m in s["sessions"]]
    others = others or {}
    unmeasured = sorted(w for w, i in others.items() if i is None)
    below = sorted(w for w, i in others.items() if i is not None and i[1] < 1)
    said = "; ".join(
        [f"{w} wasn't measured" for w in unmeasured] + [f"{w}'s interval ends below 1" for w in below]
    )
    held = {
        "confirmation": (all(k == CONFIRMATION for k in kinds), "only confirmation sessions count"),
        "pairs": (
            pairs >= rule.min_pairs and len(kinds) >= rule.min_sessions,
            f"at least {rule.min_pairs} pairs in at least {rule.min_sessions} sessions: "
            f"{pairs} in {len(kinds)}",
        ),
        "interval_above": (
            low >= rule.threshold,
            f"the pooled interval's lower end, {low:.4f}, at or above {rule.threshold}",
        ),
        "sessions_above": (
            min(medians) > 1,
            f"every session's median above 1: the least is {min(medians):.4f}",
        ),
        "others": (not unmeasured and not below, "no other workload slower" + (f": {said}" if said else "")),
        "interval_below": (
            high <= 1 / rule.threshold,
            f"the pooled interval's upper end, {high:.4f}, at or below {1 / rule.threshold:.4f}",
        ),
        "sessions_below": (
            max(medians) < 1,
            f"every session's median below 1: the most is {max(medians):.4f}",
        ),
    }
    return {
        "conditions": {k: {"held": v, "says": says} for k, (v, says) in held.items()},
        "figures": stats,
        "rule": rule.as_record(),
    }

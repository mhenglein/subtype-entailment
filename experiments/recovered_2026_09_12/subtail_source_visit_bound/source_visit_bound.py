#!/usr/bin/env python3
"""Exact Q004 source-visit counts for Subtail's EXISTING modular family.

This is not a solver for general subtype entailment or terminal BorderAvoid.
Family source: mhenglein/subtail, experiments/modular_sync_family.py at
f85ba3af769041349979e6130f1e2bc109b07c91 (C046). This implementation was
written separately. Its finite checks do not replace the all-length proof.

Python 3.9+; standard library only.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from itertools import product
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path
from typing import Dict, FrozenSet, Iterator, List, Optional, Sequence, Tuple

BASE_COMMIT = "f85ba3af769041349979e6130f1e2bc109b07c91"


@dataclass(frozen=True)
class Instance:
    delta: Tuple[Tuple[int, int], ...]
    final: FrozenSet[int]
    flags: FrozenSet[Tuple[int, int]] = frozenset()
    bad: FrozenSet[int] = frozenset()
    start: int = 0

    def __post_init__(self) -> None:
        k = len(self.delta)
        if k == 0 or not 0 <= self.start < k:
            raise ValueError("Require a nonempty state set and a valid start")
        if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < k
                                  for q in row) for row in self.delta):
            raise ValueError("Each binary transition must be -1 or a state")
        used = set(self.final) | set(self.bad)
        used.update(q for pair in self.flags for q in pair)
        if any(type(q) is not int or not 0 <= q < k for q in used):
            raise ValueError("Invalid state in an annotation")
        if any(self.delta[q] != (-1, -1) for q in self.final):
            raise ValueError("Every final state must be terminal")

    @property
    def sources(self) -> FrozenSet[int]:
        return frozenset(p for p, _ in self.flags)

    def run(self, word: str) -> Optional[Tuple[int, ...]]:
        q = self.start
        history = [q]
        for a in word:
            if a not in "01":
                return None
            q = self.delta[q][ord(a) - ord("0")]
            if q == -1:
                return None
            history.append(q)
        return tuple(history)

    def admissible(self, word: str) -> bool:
        run = self.run(word)
        return (run is not None and run[-1] in self.final
                and not any(q in self.bad for q in run))


def witness_forward(I: Instance, w: str) -> bool:
    """Literal cut-pair definition, including i=j and j=len(w)."""
    run = I.run(w)
    if run is None or run[-1] not in I.final or set(run) & I.bad:
        return False
    for i, p in enumerate(run):
        for j in range(i, len(run)):
            if (p, run[j]) in I.flags and w.startswith(w[j:], i):
                return False
    return True


def witness_reverse(I: Instance, w: str) -> bool:
    """Separate oracle: borders of every prefix of the reversed word."""
    run = I.run(w)
    if run is None or run[-1] not in I.final or set(run) & I.bad:
        return False
    rev, states = w[::-1], run[::-1]
    for end in range(len(rev) + 1):
        prefix = rev[:end]
        for b in range(end + 1):
            if prefix[:b] == prefix[end-b:] and (states[end], states[b]) in I.flags:
                return False
    return True


def source_visits(I: Instance, w: str) -> int:
    run = I.run(w)
    if run is None:
        raise ValueError("Source visits require a defined run")
    return sum(q in I.sources for q in run)


@dataclass(frozen=True)
class Family:
    periods: Tuple[int, ...]
    instance: Instance
    entries: Tuple[int, ...]
    cycles: Tuple[Tuple[int, ...], ...]

    @property
    def common_multiple(self) -> int:
        return lcm(*self.periods)

    @property
    def min_source_visits(self) -> int:
        return (len(self.periods) - 1) * (self.common_multiple + 1)

    @property
    def shortest_length(self) -> int:
        return len(self.periods) * (self.common_multiple + 1)


def make_family(periods: Sequence[int]) -> Family:
    ps = tuple(periods)
    if len(ps) < 2 or any(type(p) is not int or p <= 0 for p in ps):
        raise ValueError("At least two positive integer periods are required")
    entries: List[int] = []
    cursor = 0
    for p in ps:
        entries.append(cursor)
        cursor += p + 1
    final = cursor
    table = [[-1, -1] for _ in range(final + 1)]
    cycles = []
    for i, p in enumerate(ps):
        cycle = tuple(entries[i] + d for d in range(1, p + 1))
        cycles.append(cycle)
        table[entries[i]][1] = cycle[0]
        for d, q in enumerate(cycle):
            table[q][1] = cycle[(d + 1) % p]
        table[cycle[-1]][0] = entries[i + 1] if i + 1 < len(ps) else final
    flags = set()
    for i in range(len(ps) - 1):
        flags.update((entries[i], q) for q in cycles[-1])
        flags.update((q, entries[-1]) for q in cycles[i])
    I = Instance(tuple(tuple(row) for row in table), frozenset({final}),
                 frozenset(flags))
    return Family(ps, I, tuple(entries), tuple(cycles))


def word_from_counts(ns: Sequence[int]) -> str:
    if not ns or any(type(n) is not int or n <= 0 for n in ns):
        raise ValueError("Every block count must be a positive integer")
    return "".join("1" * n + "0" for n in ns)


def parse_counts(ps: Sequence[int], w: str) -> Optional[Tuple[int, ...]]:
    """Arithmetic language oracle; does not consult any automaton."""
    parts = w.split("0")
    if len(parts) != len(ps) + 1 or parts[-1] != "":
        return None
    blocks = parts[:-1]
    if any(not b or any(a != "1" for a in b) for b in blocks):
        return None
    ns = tuple(len(b) for b in blocks)
    return ns if all(n % p == 0 for n, p in zip(ns, ps)) else None


def arithmetic_witness(ps: Sequence[int], w: str) -> bool:
    ns = parse_counts(ps, w)
    return ns is not None and len(set(ns)) == 1


def accepted_words_through(I: Instance, limit: int) -> Iterator[str]:
    """Enumerate all accepted paths up to a length limit, not a guessed schema."""
    stack = [("", I.start)]
    while stack:
        w, q = stack.pop()
        if q in I.bad:
            continue
        if q in I.final:
            yield w
        if len(w) < limit:
            for a, nxt in enumerate(I.delta[q]):
                if nxt != -1:
                    stack.append((w + str(a), nxt))


def live_flag_certificates(F: Family) -> List[Dict[str, object]]:
    """Every flag is genuinely violated by some accepted word in this case.

    Requires each earlier period to be coprime to the last one. A certificate
    is NOT a witness: it certifies an actual forbidden comparison for a flag.
    """
    ps, I = F.periods, F.instance
    last = ps[-1]
    if any(gcd(p, last) != 1 for p in ps[:-1]):
        raise ValueError("Liveness construction needs coprime earlier/last periods")
    certs = []
    for i, p in enumerate(ps[:-1]):
        # Earlier entry -> a particular state in the last cycle.
        for d in range(1, last + 1):
            a = next(p * t for t in range(1, last + 1) if (p * t + d) % last == 0)
            ns = list(ps)
            ns[i], ns[-1] = a, a + d
            starts = [sum(n + 1 for n in ns[:j]) for j in range(len(ns))]
            pair = (F.entries[i], F.cycles[-1][d - 1])
            certs.append({"flag": list(pair), "block_counts": ns,
                          "source_cut": starts[i], "target_cut": starts[-1] + d})
        # A particular earlier cycle state -> the last entry.
        for d in range(1, p + 1):
            a = next(last * t for t in range(1, p + 1) if (last * t + d) % p == 0)
            ns = list(ps)
            ns[i], ns[-1] = a + d, a
            starts = [sum(n + 1 for n in ns[:j]) for j in range(len(ns))]
            pair = (F.cycles[i][d - 1], F.entries[-1])
            certs.append({"flag": list(pair), "block_counts": ns,
                          "source_cut": starts[i] + d, "target_cut": starts[-1]})
    # Each certificate is checked directly, not via the arithmetic classification.
    certified = set()
    for cert in certs:
        w = word_from_counts(cert["block_counts"])
        a, b = cert["source_cut"], cert["target_cut"]
        run = I.run(w)
        pair = tuple(cert["flag"])
        if not (I.admissible(w) and 0 <= a <= b <= len(w)
                and (run[a], run[b]) == pair and pair in I.flags
                and w.startswith(w[b:], a)):
            raise AssertionError(("Invalid live-flag certificate", cert))
        certified.add(pair)
    if certified != I.flags or len(certs) != len(I.flags):
        raise AssertionError("Liveness certificates did not cover exactly all flags")
    return certs


def first_primes(n: int) -> Tuple[int, ...]:
    out = []
    p = 2
    while len(out) < n:
        if all(p % d for d in range(2, isqrt(p) + 1)):
            out.append(p)
        p += 1
    return tuple(out)


def describe(F: Family) -> Dict[str, object]:
    return {"periods": list(F.periods), "states": len(F.instance.delta),
            "flags": len(F.instance.flags), "source_states": len(F.instance.sources),
            "lcm": F.common_multiple, "min_source_visits_from_proof": F.min_source_visits,
            "shortest_length_from_proof": F.shortest_length}


def self_test() -> Dict[str, object]:
    counts = Counter()

    # Explicit definition edge cases, separate from the modular family.
    empty_ok = Instance(((-1, -1),), frozenset({0}))
    empty_bad = Instance(((-1, -1),), frozenset({0}), frozenset({(0, 0)}))
    empty_unsafe = Instance(((-1, -1),), frozenset({0}), bad=frozenset({0}))
    final_column = Instance(((-1, 1), (-1, -1)), frozenset({1}), frozenset({(0, 1)}))
    diagonal = Instance(((-1, 1), (-1, -1)), frozenset({1}), frozenset({(0, 0)}))
    other_final = Instance(((1, 2), (-1, -1), (-1, -1)), frozenset({1, 2}),
                           frozenset({(0, 1)}))
    for I, w, expected in ((empty_ok, "", True), (empty_bad, "", False),
                            (empty_unsafe, "", False), (final_column, "1", False),
                            (diagonal, "1", False), (other_final, "0", False),
                            (other_final, "1", True), (empty_ok, "0", False),
                            (empty_ok, "x", False)):
        assert witness_forward(I, w) == witness_reverse(I, w) == expected
        counts["boundary_cases"] += 1

    # Repository's two-source regression: a later loop deletion creates a new
    # violation at an earlier source. This refutes that splice, not Q004.
    regression = Instance(((1, 2), (4, 1), (3, 2), (1, 0), (-1, -1)),
                          frozenset({4}), frozenset({(0, 1), (2, 0)}))
    assert witness_forward(regression, "110010")
    assert witness_reverse(regression, "110010")
    assert regression.admissible("10010")
    assert not witness_forward(regression, "10010")
    assert not witness_reverse(regression, "10010")
    counts["sequential_compression_regressions"] += 1

    # Check the generator against the repository's explicitly printed table.
    primary = make_family((2, 3)).instance
    assert primary.delta == ((-1, 1), (-1, 2), (3, 1), (-1, 4),
                             (-1, 5), (-1, 6), (7, 4), (-1, -1))
    assert primary.flags == frozenset({(0, 4), (0, 5), (0, 6), (1, 3), (2, 3)})
    counts["printed_repository_fixture_checks"] += 1

    # All binary strings through the displayed bound (including rejected paths).
    raw_cases = [((1, 1), 10), ((1, 2), 10), ((2, 2), 10),
                 ((2, 3), 14), ((1, 2, 3), 10)]
    for ps, limit in raw_cases:
        F = make_family(ps)
        for n in range(limit + 1):
            for bits in product("01", repeat=n):
                w = "".join(bits)
                assert F.instance.admissible(w) == (parse_counts(ps, w) is not None)
                assert witness_forward(F.instance, w) == witness_reverse(F.instance, w) == arithmetic_witness(ps, w)
                counts["raw_binary_word_comparisons"] += 1

    # Independent accepted-path enumeration, including every shorter accepted word.
    path_cases = [((2, 3), 14), ((2, 3, 5), 93)]
    path_results = []
    for ps, limit in path_cases:
        F = make_family(ps)
        found = []
        checked = 0
        for w in accepted_words_through(F.instance, limit):
            checked += 1
            answer = witness_forward(F.instance, w)
            assert answer == witness_reverse(F.instance, w) == arithmetic_witness(ps, w)
            ns = parse_counts(ps, w)
            assert ns is not None
            assert source_visits(F.instance, w) == sum(n + 1 for n in ns[:-1])
            if answer:
                found.append(w)
        assert found == [word_from_counts((F.common_multiple,) * len(ps))]
        assert source_visits(F.instance, found[0]) == F.min_source_visits
        counts["complete_accepted_path_comparisons"] += checked
        path_results.append({**describe(F), "word_length_limit": limit,
                             "accepted_paths_checked": checked,
                             "witnesses_at_or_below_limit": len(found),
                             "shortest_witness": found[0],
                             "source_visits_of_shortest_witness": source_visits(F.instance, found[0])})

    # Arbitrary periods and lengths, not just pairwise-coprime prime examples.
    period_cases = list(product(range(1, 6), repeat=2))
    period_cases += list(product(range(1, 4), repeat=3))
    period_cases += [(2, 3, 5, 7)]
    for ps in period_cases:
        F = make_family(ps)
        expected_sources = frozenset(q for i in range(len(ps) - 1)
                                     for q in (F.entries[i],) + F.cycles[i])
        assert F.instance.sources == expected_sources
        assert len(F.instance.delta) == 1 + len(ps) + sum(ps)
        for multipliers in product(range(1, 5), repeat=len(ps)):
            ns = tuple(p * t for p, t in zip(ps, multipliers))
            w = word_from_counts(ns)
            assert F.instance.admissible(w)
            assert witness_forward(F.instance, w) == witness_reverse(F.instance, w) == (len(set(ns)) == 1)
            assert source_visits(F.instance, w) == sum(n + 1 for n in ns[:-1])
            counts["exponent_vector_comparisons"] += 1

    # Materialize a few certified least witnesses, rather than only their counts.
    for ps in [(2, 3), (2, 3, 5), (2, 3, 5, 7)]:
        F = make_family(ps)
        w = word_from_counts((F.common_multiple,) * len(ps))
        assert witness_forward(F.instance, w) and witness_reverse(F.instance, w)
        assert len(w) == F.shortest_length
        assert source_visits(F.instance, w) == F.min_source_visits
        counts["materialized_least_witness_checks"] += 1

    # Arithmetic large examples: do not materialize huge words or call them searched.
    prime_rows, liveness = [], []
    primes = first_primes(10)
    for r in range(2, 11):
        F = make_family(primes[:r])
        assert F.common_multiple == prod(primes[:r])
        certs = live_flag_certificates(F)
        counts["individually_checked_live_flags"] += len(certs)
        row = describe(F)
        row["all_flags_certified_live"] = True
        row["large_lengths_computed_arithmetically_not_enumerated"] = r >= 5
        prime_rows.append(row)
        liveness.append({"periods": list(F.periods), "certificates": certs})

    return {"status": "PASS", "scope": "Existing modular family only; not a general SEP decision",
            "base_commit": BASE_COMMIT, "counts": dict(sorted(counts.items())),
            "raw_search_ranges": [{"periods": list(ps), "max_word_length": limit}
                                  for ps, limit in raw_cases],
            "complete_path_searches": path_results, "prime_family": prime_rows,
            "live_flag_certificates": liveness,
            "evidence_limits": ["Finite tests are regression evidence, not the all-length proof.",
                "Minimum source visits over all lengths and the prime asymptotic rely on the accompanying proof.",
                "No general computable source-visit bound is established or refuted.",
                "No Lean check or independent mathematical review was performed.",
                "The modular construction is prior repository work, not a claimed new construction."]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--periods", type=int, nargs="+", help="Describe this modular family")
    mode.add_argument("--self-test", action="store_true", help="Run the finite independent checks")
    parser.add_argument("--output", type=Path, help="Save complete JSON output")
    args = parser.parse_args()
    if args.self_test and not __debug__:
        parser.error("Run the self-test without -O: its assertions must execute")
    try:
        result = self_test() if args.self_test else describe(make_family(args.periods))
    except ValueError as exc:
        parser.error(str(exc))
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    # Omit the large per-flag appendix from stdout; it is preserved in --output.
    brief = {k: v for k, v in result.items() if k != "live_flag_certificates"}
    print(json.dumps(brief, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

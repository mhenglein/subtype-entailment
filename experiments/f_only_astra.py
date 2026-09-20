#!/usr/bin/env python3
"""Independent F-only checks. No imports from Subtail implementations.

Search failures are UNKNOWN. Found minima are certified by complete enumeration
of all shorter binary words. Finishing BFS exhausts its finite product but is
only a test of the new finishing definition, not a proof of the global F bound.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import platform
import random
import time
from collections import Counter, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

Word = tuple[int, ...]

@dataclass(frozen=True)
class Instance:
    transitions: tuple[tuple[int | None, int | None], ...]
    initial: int
    final: frozenset[int]
    bad: frozenset[int] = frozenset()
    flags: frozenset[tuple[int, int]] = frozenset()

    @property
    def k(self) -> int:
        return len(self.transitions)

    def validate(self) -> None:
        assert 0 <= self.initial < self.k
        assert all(q is None or 0 <= q < self.k
                   for row in self.transitions for q in row)
        assert all(self.transitions[f] == (None, None) for f in self.final)
        assert all(0 <= q < self.k for q in self.final | self.bad)
        assert all(0 <= p < self.k and 0 <= q < self.k for p, q in self.flags)


def words(n: int) -> Iterable[Word]:
    return itertools.product((0, 1), repeat=n)


def run(I: Instance, w: Word, start: int | None = None) -> tuple[int, ...] | None:
    q = I.initial if start is None else start
    path = [q]
    for a in w:
        q = I.transitions[q][a]
        if q is None:
            return None
        path.append(q)
    return tuple(path)


def witness(I: Instance, w: Word) -> bool:
    """Literal forward predicate: every ordered pair of cuts, no KMP."""
    c = run(I, w)
    if c is None or c[-1] not in I.final or any(q in I.bad for q in c):
        return False
    n = len(w)
    for j in range(n + 1):
        for i in range(j + 1):
            if (c[i], c[j]) in I.flags and w[j:] == w[i:i + n - j]:
                return False
    return True


def borders(w: Word) -> tuple[int, ...]:
    n = len(w)
    return tuple(b for b in range(n + 1) if w[:b] == w[n - b:])


def rank(w: Word) -> int:
    return len(borders(w)) - 1


def safe_reference(I: Instance, b: Word, labels: tuple[int, ...]) -> bool:
    """Literal reversed border predicate, separately implemented."""
    if not b or len(labels) != len(b) + 1 or labels[0] not in I.final:
        return False
    if any(q in I.bad for q in labels):
        return False
    for j, a in enumerate(b):
        if I.transitions[labels[j + 1]][a] != labels[j]:
            return False
    for j, q in enumerate(labels):
        for h in borders(b[:j]):
            if (q, labels[h]) in I.flags:
                return False
    return True


def parent(b: Word) -> int:
    return max(h for h in borders(b) if h < len(b))


def advance(b: Word, cursor: int, a: int) -> int:
    v = b[:cursor] + (a,)
    return max(h for h in range(min(len(b), len(v)) + 1)
               if b[:h] == v[len(v) - h:])


def no_early_return(b: Word, c: Word) -> bool:
    """The final cut is deliberately excluded; overlaps are included."""
    assert c[:len(b)] == b
    return all(len(b) not in borders(c[:j])
               for j in range(len(b) + 1, len(c)))


def finishing(I: Instance, b: Word, labels: tuple[int, ...],
              allow_final_return: bool = True) -> tuple[Word | None, int]:
    """Shortest product path for the proposed k-control observer.

    End is allowed only with control initial, and has no outgoing observer
    transition. All mask tests refer to the SAME fixed reference b.
    """
    assert safe_reference(I, b, labels)
    start = (parent(b), labels[-1])
    queue = deque([start])
    prev: dict[tuple[int, int], tuple[tuple[int, int], int] | None] = {start: None}
    end: tuple[int, int] | None = None
    while queue:
        v, q = queue.popleft()
        if q == I.initial:
            end = (v, q)
            break
        if v == len(b):
            continue
        for a in (0, 1):
            u = advance(b, v, a)
            for p in range(I.k):
                if I.transitions[p][a] != q or p in I.bad or (p, p) in I.flags:
                    continue
                if u == len(b) and (not allow_final_return or p != I.initial):
                    continue
                if any((p, labels[h]) in I.flags for h in borders(b[:u])):
                    continue
                nxt = (u, p)
                if nxt not in prev:
                    prev[nxt] = ((v, q), a)
                    queue.append(nxt)
    if end is None:
        return None, len(prev)
    ext = []
    p = end
    while prev[p] is not None:
        p, a = prev[p]  # type: ignore[misc]
        ext.append(a)
    ext.reverse()
    w = tuple(reversed(b + tuple(ext)))
    assert witness(I, w), (I, b, labels, w)
    assert no_early_return(b, tuple(reversed(w)))
    assert len(ext) + 1 <= (len(b) + 1) * I.k
    return w, len(prev)


def shortest(I: Instance, cap: int) -> Word | None:
    for n in range(cap + 1):
        for w in words(n):
            if witness(I, w):
                return w
    return None


def check_minimum(I: Instance, w: Word, counts: Counter) -> None:
    """w has been found by exhaustive increasing-length enumeration."""
    c = run(I, w)
    assert c is not None and witness(I, w)
    counts['found_shortest_witnesses'] += 1
    counts[f'shortest_length_{len(w)}'] += 1
    # A return to the initial state permits suffix truncation without a join.
    assert I.initial not in c[1:]
    if not w:
        return
    rho = tuple(reversed(w))
    labels = tuple(reversed(c))
    assert safe_reference(I, rho, labels)
    if len(w) == 1:
        counts['one_letter_witnesses'] += 1
        return
    depths = [rank(rho[:j]) for j in range(len(rho))]
    assert max(depths) <= I.k - 2
    height = max(depths)
    milestones = [next(j for j, d in enumerate(depths) if d >= h)
                  for h in range(1, height + 1)]
    assert milestones[0] == 1
    assert len(milestones) - 1 <= I.k - 3
    for h, m in enumerate(milestones, start=1):
        assert depths[m] == h
    for m, n in zip(milestones, milestones[1:]):
        assert parent(rho[:n]) == m
        assert m in borders(rho[:n])
        assert all(m not in borders(rho[:j]) for j in range(m + 1, n))
    m = milestones[-1]
    assert no_early_return(rho[:m], rho)
    new, explored = finishing(I, rho[:m], labels[:m + 1])
    assert new is not None
    assert len(new) >= len(w), 'Input was not globally shortest'
    counts['max_product_explored'] = max(counts['max_product_explored'], explored)
    counts[f'milestone_promotions_{height - 1}'] += 1
    old, _ = finishing(I, rho[:m], labels[:m + 1], False)
    if old is None:
        counts['old_finish_fails_new_finish_succeeds'] += 1
    if m in borders(rho):
        counts['final_return_in_original_minimum'] += 1
        if len(rho) < 2 * m:
            counts['overlapping_final_return_in_minimum'] += 1


def census_three(cap: int, counts: Counter) -> None:
    """All 3-state tables with initial0, sole terminal final2; all 512 G.

    Bad is empty in this particular census. No negative answer is claimed
    when all words through cap are rejected.
    """
    choices = (None, 0, 1, 2)
    pair_list = tuple(itertools.product(range(3), repeat=2))
    for entries in itertools.product(choices, repeat=4):
        table = ((entries[0], entries[1]), (entries[2], entries[3]), (None, None))
        bare = Instance(table, 0, frozenset({2}))
        accepted = []
        for n in range(cap + 1):
            for w in words(n):
                c = run(bare, w)
                if c is None or c[-1] != 2:
                    continue
                mask = 0
                for j in range(n + 1):
                    for i in range(j + 1):
                        if w[j:] == w[i:i + n - j]:
                            mask |= 1 << (3 * c[i] + c[j])
                accepted.append((w, mask))
        for bits in range(512):
            flags = frozenset(pair_list[i] for i in range(9) if bits >> i & 1)
            I = Instance(table, 0, frozenset({2}), flags=flags)
            found = next((w for w, profile in accepted if not bits & profile), None)
            counts['three_state_annotations'] += 1
            if found is None:
                counts['three_state_no_witness_through_cap_UNKNOWN'] += 1
            else:
                # The profile enumeration used all words at every earlier length.
                check_minimum(I, found, counts)


def random_checks(seed: int, trials: int, cap: int, counts: Counter) -> None:
    rng = random.Random(seed)
    for _ in range(trials):
        k = rng.randint(3, 8)
        final = frozenset(q for q in range(k) if rng.random() < 0.15) or frozenset({k-1})
        table = tuple((None, None) if q in final else
                      tuple(rng.choice([None] + list(range(k))) for _ in (0, 1))
                      for q in range(k))
        flags = frozenset((p, q) for p in range(k) for q in range(k)
                          if rng.random() < (0.015 if p == q else 0.1))
        bad = frozenset(q for q in range(k) if rng.random() < 0.025)
        I = Instance(table, rng.randrange(k), final, bad, flags)
        I.validate()
        found = shortest(I, cap)
        counts['random_instances'] += 1
        if found is None:
            counts['random_no_witness_through_cap_UNKNOWN'] += 1
        else:
            check_minimum(I, found, counts)
        # Literal arbitrary safe suffixes, not only rank-selected references.
        for _ in range(6):
            u = tuple(rng.randrange(2) for _ in range(rng.randint(1, 4)))
            q = rng.randrange(k)
            labels_forward = run(I, u, q)
            if labels_forward is None:
                continue
            b = tuple(reversed(u))
            labels = tuple(reversed(labels_forward))
            if not safe_reference(I, b, labels):
                continue
            out, _ = finishing(I, b, labels)
            counts['arbitrary_safe_reference_soundness_checks'] += 1
            # Only positive bounded completions are used for completeness tests.
            # Failure to find a literal completion here is NOT an all-length NO.
            for d in range(5):
                for prefix in words(d):
                    full = prefix + u
                    full_run = run(I, full)
                    if full_run is None or full_run[d:] != labels_forward:
                        continue
                    if witness(I, full) and no_early_return(b, tuple(reversed(full))):
                        assert out is not None
                        counts['literal_bounded_completion_coverage_checks'] += 1
        # Cross-check the two literal orientations on a separate bounded corpus.
        for _ in range(8):
            w = tuple(rng.randrange(2) for _ in range(rng.randrange(cap + 1)))
            c = run(I, w)
            rev_truth = bool(w) and c is not None and safe_reference(
                I, tuple(reversed(w)), tuple(reversed(c)))
            if w:
                assert witness(I, w) == rev_truth
                counts['literal_forward_reverse_checks'] += 1
            if c is not None and witness(I, w):
                for j, q in enumerate(c):
                    if q == I.initial:
                        assert witness(I, w[j:])
                        counts['initial_return_suffix_checks'] += 1


def boundary_and_recurrent(counts: Counter) -> None:
    # All one/two-state terminal tables, final sets, Bad sets and flags.
    for k in (1, 2):
        for entries in itertools.product((None,) + tuple(range(k)), repeat=2*k):
            table = tuple(tuple(entries[2*q:2*q+2]) for q in range(k))
            for finals in range(1 << k):
                F = frozenset(q for q in range(k) if finals >> q & 1)
                if any(table[q] != (None, None) for q in F):
                    continue
                for bad in range(1 << k):
                    B = frozenset(q for q in range(k) if bad >> q & 1)
                    for flags in range(1 << (k*k)):
                        G = frozenset((p,q) for p in range(k) for q in range(k)
                                      if flags >> (p*k+q) & 1)
                        for initial in range(k):
                            I = Instance(table, initial, F, B, G)
                            found = shortest(I, 5)
                            if found is not None:
                                assert len(found) <= (0 if k == 1 else 1)
                            counts['one_two_state_annotations'] += 1
    # The published recurrent residual fixture, with shared exponents.
    I = Instance(((None,1),(2,1),(2,3),(4,3),(None,None)), 0,
                 frozenset({4}), flags=frozenset({(0,3),(1,2)}))
    for m in range(1, 7):
        for z in range(1, 5):
            for n in range(1, 7):
                w = (1,)*m + (0,)*z + (1,)*n + (0,)
                assert witness(I, w) == (m == n)
                counts['recurrent_shared_parameter_cases'] += 1
    check_minimum(I, shortest(I, 6), counts)  # type: ignore[arg-type]
    # Explicit final-return boundary: unary path0->1->2.
    J = Instance(((1,None),(2,None),(None,None)),0,frozenset({2}))
    old,_ = finishing(J, (0,), (2,1), False)
    new,_ = finishing(J, (0,), (2,1), True)
    assert old is None and new == (0,0)
    counts['required_final_return_regression'] += 1
    # Overlapping first return at the final cut, unary 4-state path.
    K = Instance(((1,None),(2,None),(3,None),(None,None)),0,frozenset({3}))
    old,_ = finishing(K, (0,0), (3,2,1), False)
    new,_ = finishing(K, (0,0), (3,2,1), True)
    assert old is None and new == (0,0,0)
    counts['required_overlapping_final_return_regression'] += 1
    check_minimum(K, (0,0,0), counts)
    # Each chain has exactly ONE accepted word, giving an all-length oracle.
    for k in range(3, 11):
        table = tuple((q+1, None) for q in range(k-1)) + ((None, None),)
        chain = Instance(table, 0, frozenset({k-1}))
        w = (0,)*(k-1)
        check_minimum(chain, w, counts)
        counts['unique_accepted_word_chain_oracles'] += 1
        b = (0,)*(k-2)
        labels = tuple(range(k-1, 0, -1))
        assert rank(b) == k-2
        for target in range(k):
            blocked = Instance(table, 0, frozenset({k-1}),
                               flags=frozenset({(0, target)}))
            assert not witness(blocked, w)
            # B avoids state0, so it stays safe. The NEW cut must reject each
            # possible diagonal, nonempty-border and empty-border flag.
            assert safe_reference(blocked, b, labels)
            out, _ = finishing(blocked, b, labels)
            assert out is None
            counts['certified_unique_word_negative_mask_oracles'] += 1
    # Normalization works on arbitrary witnesses, not only shortest ones.
    looping = Instance(((1,0),(2,None),(None,None)),0,frozenset({2}))
    for n in range(1, 21):
        w = (1,)*n + (0,0)
        assert witness(looping, w)
        c = run(looping, w)
        assert c is not None
        last = max(i for i, q in enumerate(c) if q == looping.initial)
        reduced = w[last:]
        assert reduced == (0,0) and witness(looping, reduced)
        assert looping.initial not in run(looping, reduced)[1:]
        counts['last_initial_visit_normalization_cases'] += 1


def arithmetic_checks(counts: Counter) -> None:
    # Only the first lag step is expanded. Higher tower levels are not computed.
    for k in range(1, 51):
        x = k + 10
        a = 64*k
        y = a * x ** (2*x + 2)
        assert 6*x*x <= y
        assert a <= x**4
        # Verify the symbolic exponent inequalities used by the inductive proof.
        assert 12*x*x+14 <= 4*y+4
        counts['lag_base_integer_checks'] += 1
    for x in range(3, 101):
        for y in (6*x*x, 6*x*x+1, 7*x*x):
            assert 12*x*x + 14 <= 4*y + 4
            counts['lag_exponent_checks'] += 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=int, default=2026092069)
    parser.add_argument('--trials', type=int, default=1000)
    parser.add_argument('--word-cap', type=int, default=10)
    parser.add_argument('--census-cap', type=int, default=8)
    parser.add_argument('--output', type=Path, default=Path('results/f-only-astra.json'))
    args = parser.parse_args()
    start = time.monotonic()
    counts: Counter = Counter()
    boundary_and_recurrent(counts)
    census_three(args.census_cap, counts)
    random_checks(args.seed, args.trials, args.word_cap, counts)
    arithmetic_checks(counts)
    result = {
        'status': 'PASS_BOUNDED_CHECKS_NOT_GLOBAL_PROOF',
        'base_revision': '19b06d4fed9da635d9b911f0e908d04e4fc4b099',
        'seed': args.seed, 'random_trials': args.trials,
        'random_word_length_cap': args.word_cap,
        'three_state_word_length_cap': args.census_cap,
        'negative_search_semantics': 'UNKNOWN unless an independent all-length proof is supplied',
        'three_state_scope': 'initial0, sole terminal final2, no Bad, all 256 tables and all 512 ordered flag sets',
        'counts': dict(sorted(counts.items())),
        'python': platform.python_version(), 'platform': platform.platform(),
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'elapsed_seconds': round(time.monotonic() - start, 6),
        'independent_mathematical_review': 'NOT_ASSESSED_BY_THIS_HARNESS',
        'new_Lean_check': 'SEPARATE_WORKFLOW_NOT_MEASURED_BY_THIS_HARNESS',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent C030 checks against exact regular-tree semantics.

Input inspected: mhenglein/subtail at
064fc7306b679bf607b91e7d8de259823f200c62.
No repository imports, no network access, no shared-file writes.
Words/instances are bounded in the test corpus. Each tree-language inclusion
and prefix-closure check is exact: finite derivative graphs are exhausted.
This is not a Lean proof or a replay of the repository's E021 script.
"""
from __future__ import annotations
import argparse
import itertools
import json
import random
import time
from dataclasses import dataclass
from pathlib import Path

REVISION = '064fc7306b679bf607b91e7d8de259823f200c62'

@dataclass(frozen=True)
class Instance:
    delta: tuple[tuple[int, int], ...]
    final: frozenset[int]
    flags: frozenset[tuple[int, int]] = frozenset()
    bad: frozenset[int] = frozenset()
    start: int = 0

    def trace(self, word: str) -> tuple[int, ...]:
        out = [self.start]
        for a in word:
            q = self.delta[out[-1]][int(a)]
            if q < 0:
                break
            out.append(q)
        return tuple(out)


def direct_witness(I: Instance, w: str) -> bool:
    qs = I.trace(w)
    if len(qs) != len(w) + 1 or qs[-1] not in I.final:
        return False
    if any(q in I.bad for q in qs):
        return False
    # Literal Basic.Witness convention: later suffix is a prefix of earlier.
    for j in range(len(w) + 1):
        for i in range(j + 1):
            if w[i:].startswith(w[j:]) and (qs[i], qs[j]) in I.flags:
                return False
    return True


def normalized_constraints(I: Instance) -> tuple[tuple, ...]:
    k = len(I.delta)
    b = 2*k
    cs = [('denial', b)]
    for q, row in enumerate(I.delta):
        cs.append(('upper', q, *(b if r < 0 else r for r in row)))
        if q not in I.final:
            cs.append(('lower', *(b if r < 0 else k+r for r in row), k+q))
    cs.extend(('leq', p, k+q) for p, q in sorted(I.flags))
    cs.extend(('denial', q) for q in sorted(I.bad))
    return tuple(cs)

# A derivative state (R,T) denotes a union of lower-copy residuals V_r,
# r in R, and finite singleton languages {t}, t in T. The invariant adds
# S_r to T for every r in R. No stack-saturation implementation is used.
State = tuple[frozenset[int], frozenset[str]]

class SemanticModel:
    def __init__(self, I: Instance, seed_word: str | None):
        self.I = I
        self.k = len(I.delta)
        self.a = [set() for _ in I.delta]
        if seed_word is not None:
            for i, q in enumerate(I.trace(seed_word)):
                suffix = seed_word[i:]
                self.a[q].update(suffix[:j] for j in range(len(suffix)+1))
        self.sources = [set() for _ in I.delta]
        for p, q in I.flags:
            self.sources[q].update(self.a[p])
        self._steps: dict[tuple[State, int], State] = {}
        self._accepts: dict[State, bool] = {}
        self._inclusions: dict[tuple[State, State], bool] = {}
        self._closed: dict[State, bool] = {}
        self.empty: State = (frozenset(), frozenset())
        self.rho = tuple(self.finite(x) for x in self.a) + tuple(
            self.make({q}, set()) for q in range(self.k)) + (self.empty,)

    def finite(self, words: set[str]) -> State:
        return frozenset(), frozenset(words)

    def make(self, states: set[int], words: set[str]) -> State:
        for q in states:
            words.update(self.sources[q])
        return frozenset(states), frozenset(words)

    def accepts(self, state: State) -> bool:
        if state not in self._accepts:
            rs, ts = state
            self._accepts[state] = '' in ts or any(q not in self.I.final for q in rs)
        return self._accepts[state]

    def step(self, state: State, a: int) -> State:
        key = state, a
        if key not in self._steps:
            rs, ts = state
            targets = {self.I.delta[q][a] for q in rs if self.I.delta[q][a] >= 0}
            tails = {t[1:] for t in ts if t and int(t[0]) == a}
            self._steps[key] = self.make(targets, tails)
        return self._steps[key]

    def contains(self, variable: int, word: str) -> bool:
        s = self.rho[variable]
        for a in word:
            s = self.step(s, int(a))
        return self.accepts(s)

    def included(self, x: State, y: State) -> bool:
        key = x, y
        if key in self._inclusions:
            return self._inclusions[key]
        todo = [key]
        seen = {key}
        result = True
        for lhs, rhs in todo:
            if self.accepts(lhs) and not self.accepts(rhs):
                result = False
                break
            for a in (0, 1):
                pair = self.step(lhs, a), self.step(rhs, a)
                if pair not in seen:
                    seen.add(pair)
                    todo.append(pair)
        self._inclusions[key] = result
        return result

    def prefix_closed(self, start: State) -> bool:
        if start in self._closed:
            return self._closed[start]
        todo = [(start, False)]
        seen = set(todo)
        result = True
        for state, missing_prefix in todo:
            here = self.accepts(state)
            if here and missing_prefix:
                result = False
                break
            for a in (0, 1):
                pair = self.step(state, a), missing_prefix or not here
                if pair not in seen:
                    seen.add(pair)
                    todo.append(pair)
        self._closed[start] = result
        return result

    def errors(self, constraints: tuple[tuple, ...], word: str | None) -> list:
        failures = []
        for q, state in enumerate(self.rho):
            if not self.prefix_closed(state):
                failures.append(('not_prefix_closed', q))
        for clause in constraints:
            tag, *xs = clause
            if tag == 'denial':
                good = self.included(self.rho[xs[0]], self.empty)
            elif tag == 'leq':
                good = self.included(self.rho[xs[0]], self.rho[xs[1]])
            elif tag == 'upper':
                q, left, right = xs
                good = all(self.included(self.step(self.rho[q], a), self.rho[r])
                           for a, r in enumerate((left, right)))
            elif tag == 'lower':
                left, right, q = xs
                good = self.accepts(self.rho[q]) and all(
                    self.included(self.rho[r], self.step(self.rho[q], a))
                    for a, r in enumerate((left, right)))
            else:
                raise ValueError(clause)
            if not good:
                failures.append(clause)
        if word is not None:
            if not self.contains(self.I.start, word):
                failures.append('alpha_missing')
            if self.contains(self.k+self.I.start, word):
                failures.append('beta_present')
        return failures


def words(max_length: int):
    for length in range(max_length+1):
        for w in itertools.product('01', repeat=length):
            yield ''.join(w)


def exhaustive(k: int):
    rows = list(itertools.product(range(-1, k), repeat=2))
    # Each state can be nonfinal with any row, or final with the terminal row.
    choices = [(row, False) for row in rows] + [((-1, -1), True)]
    for data in itertools.product(choices, repeat=k):
        delta = tuple(row for row, _ in data)
        final = frozenset(q for q, (_, f) in enumerate(data) if f)
        for gm in range(1 << (k*k)):
            flags = frozenset((p, q) for p in range(k) for q in range(k)
                              if gm & (1 << (p*k+q)))
            for bm in range(1 << k):
                bad = frozenset(q for q in range(k) if bm & (1 << q))
                for s in range(k):
                    yield Instance(delta, final, flags, bad, s)


def fixtures():
    terminal = ((-1, -1),)
    one_edge = ((1, -1), (-1, -1))
    return [
        ('empty_accepts', Instance(terminal, frozenset({0})), ''),
        ('empty_nonfinal', Instance(terminal, frozenset()), ''),
        ('bad_initial', Instance(terminal, frozenset({0}), bad=frozenset({0})), ''),
        ('diagonal_initial', Instance(terminal, frozenset({0}), frozenset({(0,0)})), ''),
        ('forward_flag_blocks', Instance(one_edge, frozenset({1}), frozenset({(0,1)})), '0'),
        ('reverse_flag_does_not', Instance(one_edge, frozenset({1}), frozenset({(1,0)})), '0'),
        ('undefined_then_empty', Instance(one_edge, frozenset({1})), '11'),
        ('nonaccepting_terminal', Instance(one_edge, frozenset()), '0'),
        ('bad_later_state', Instance(one_edge, frozenset({1}), bad=frozenset({1})), '0'),
        ('bad_proper_prefix', Instance(((1,-1),(2,-1),(-1,-1)), frozenset({2}), bad=frozenset({1})), '00'),
        ('nonzero_start', Instance(((-1,-1),(0,-1)), frozenset({0}), start=1), '0'),
        ('infinite_lower_tree', Instance(((0,1),(-1,-1)), frozenset({1})), '0001'),
        ('unreachable_bad_flagged', Instance(((1,-1),(-1,-1),(-1,-1)), frozenset({1}),
                                            frozenset({(2,2),(2,1)}), frozenset({2})), '0'),
        ('proper_suffix_flag_blocks', Instance(((0,1),(2,-1),(2,3),(-1,-1)), frozenset({3}),
                                               frozenset({(0,1)})), '0101'),
        ('proper_suffix_flag_avoided', Instance(((0,1),(2,-1),(2,3),(-1,-1)), frozenset({3}),
                                                frozenset({(0,1)})), '01001'),
        ('multiple_returns', Instance(((0,1),(-1,-1)), frozenset({1})), '001'),
    ]


def run(suite: str, max_length: int, output: Path):
    began = time.monotonic()
    counts = {'instances': 0, 'words': 0, 'positive_words': 0,
              'exact_model_checks': 0, 'exact_satisfiability_models': 0}
    details = []
    if suite == 'fixtures':
        for name, I, w in fixtures():
            cs = normalized_constraints(I)
            assert len(cs) == 1+len(I.delta)+(len(I.delta)-len(I.final))+len(I.flags)+len(I.bad)
            baseline = SemanticModel(I, None)
            assert not baseline.errors(cs, None), name
            model = SemanticModel(I, w)
            errors = model.errors(cs, w)
            expected = direct_witness(I, w)
            assert (not errors) == expected, (name, w, errors)
            counts['instances'] += 1
            counts['words'] += 1
            counts['positive_words'] += expected
            counts['exact_model_checks'] += 1
            counts['exact_satisfiability_models'] += 1
            details.append({'name': name, 'word': w, 'witness': expected,
                            'model_separates': not errors, 'failed_checks': errors})
        # Mutation check: final states with outgoing edges are outside C030.
        # The explicit semantic language constructor is only specified for
        # terminal finals; use an actual valid countermodel of the mutated
        # one-state lower-free constraint system separately in the report.
    else:
        if suite in ('k1', 'k2'):
            inputs = exhaustive(int(suite[-1]))
        elif suite == 'random':
            rng = random.Random(2026091930)
            cases = []
            for _ in range(120):
                k = rng.randrange(3, 7)
                fs = frozenset(q for q in range(k) if rng.random() < .3)
                delta = tuple((-1,-1) if q in fs else
                              (rng.randrange(-1,k), rng.randrange(-1,k)) for q in range(k))
                gs = frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.17)
                bs = frozenset(q for q in range(k) if rng.random()<.15)
                cases.append(Instance(delta, fs, gs, bs, rng.randrange(k)))
            inputs = iter(cases)
        else:
            raise ValueError(suite)
        corpus = tuple(words(max_length))
        for I in inputs:
            cs = normalized_constraints(I)
            assert len(cs) == 1+len(I.delta)+(len(I.delta)-len(I.final))+len(I.flags)+len(I.bad)
            assert not SemanticModel(I, None).errors(cs, None), ('UNSAT?', I)
            counts['exact_satisfiability_models'] += 1
            counts['instances'] += 1
            for w in corpus:
                expected = direct_witness(I, w)
                errors = SemanticModel(I, w).errors(cs, w)
                assert (not errors) == expected, (I, w, expected, errors)
                counts['words'] += 1
                counts['positive_words'] += expected
                counts['exact_model_checks'] += 1
    result = {'status': 'PASS', 'revision_inspected': REVISION,
              'suite': suite, 'max_word_length': max_length if suite != 'fixtures' else None,
              'counts': counts, 'elapsed_seconds': round(time.monotonic()-began, 3),
              'scope': 'Bounded word/input corpus; exact full regular-tree model validation; not Lean',
              'repository_imports': False, 'fixtures': details}
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', choices=('fixtures','k1','k2','random'), default='fixtures')
    parser.add_argument('--length', type=int, default=2)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args.suite, args.length, args.output)

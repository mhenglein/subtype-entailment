"""Exact terminal one-flag decision by rational length counting.

No finite bound is assumed by the caller. The proof supplies B = m*k*(k+1)/2
for the return-free suffix, where m is its completed transition-monoid size.
The full instance has a witness of length <= B+k-2 if it is positive.
This module does not decide arbitrary multiple flags. All caps are UNKNOWN.
"""
from collections import deque
from dataclasses import dataclass
from functools import lru_cache
from typing import Optional

from border_lab import Instance, witness, border_witness


class LimitReached(Exception):
    pass


def validate(I):
    k = len(I.delta)
    if I.alphabet != '01' or not k or not 0 <= I.start < k:
        raise ValueError('A nonempty binary Instance is required')
    if any(len(row) != 2 or any(type(q) is not int or q < -1 or q >= k for q in row)
           for row in I.delta):
        raise ValueError('Malformed transition table')
    if any(type(q) is not int or not 0 <= q < k for q in I.bad | I.final):
        raise ValueError('Malformed state annotations')
    if any(len(pair) != 2 or any(type(q) is not int or not 0 <= q < k for q in pair)
           for pair in I.flags):
        raise ValueError('Malformed flag relation')
    if any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        raise ValueError('All accepting states must be terminal')


def shortest_path(I, start, finals, forbidden=frozenset()):
    if start in forbidden:
        return None
    parent = {start: None}
    queue = deque([start])
    while queue:
        q = queue.popleft()
        if q in finals:
            out = []
            while parent[q] is not None:
                q, a = parent[q]
                out.append(a)
            return ''.join(reversed(out))
        for a, t in enumerate(I.delta[q]):
            if t >= 0 and t not in forbidden and t not in parent:
                parent[t] = (q, str(a))
                queue.append(t)
    return None


@dataclass
class MonoidCounter:
    """Count candidates and period INCIDENCES from a return-free source.

    `incidences` is not a count of distinct bad words unless at most one of
    the selected target states can be a period endpoint on each word.
    """
    instance: Instance
    targets: frozenset
    max_monoid: Optional[int] = 10000
    max_work: Optional[int] = 2000000

    def __post_init__(self):
        validate(self.instance)
        I = self.instance
        k = len(I.delta)
        self.k, self.work = k, 0
        if I.bad or any(I.start in row for row in I.delta):
            raise ValueError('Counter needs a safe table with no edge back to its source')
        if self.targets & (I.final | {I.start}) or not self.targets <= set(range(k)):
            raise ValueError('Period targets must be internal states')
        for cap in (self.max_monoid, self.max_work):
            if cap is not None and (type(cap) is not int or cap < 1):
                raise ValueError('Caps must be positive integers or None')
        sink = k
        self.letters = tuple(tuple(I.delta[q][a] if I.delta[q][a] >= 0 else sink
                                   for q in range(k)) + (sink,) for a in (0, 1))
        identity = tuple(range(k+1))
        self.actions = [identity]
        index = {identity: 0}
        self.next = []
        for A in self.actions:
            row = []
            for letter in self.letters:
                B = tuple(letter[q] for q in A)
                if B not in index:
                    if self.max_monoid is not None and len(index) >= self.max_monoid:
                        raise LimitReached('transition-monoid cap')
                    index[B] = len(self.actions)
                    self.actions.append(B)
                row.append(index[B])
            self.next.append(tuple(row))
        self.m = len(self.actions)
        self.bound = self.m*k*(k+1)//2
        self.fibres = [tuple([1] + [0]*(self.m-1))]
        self.allowed = []
        for e in range(1, k):
            rows = []
            for A in self.actions:
                row = []
                for bi, B in enumerate(self.actions):
                    self.tick()
                    q = B[A[I.start]]
                    if q not in self.targets:
                        continue
                    for _ in range(e-1):
                        q = B[A[q]]
                    if A[q] in I.final:
                        row.append(bi)
                rows.append(tuple(row))
            self.allowed.append(tuple(rows))
        self.filtered = {}

    def tick(self, amount=1):
        self.work += amount
        if self.max_work is not None and self.work > self.max_work:
            raise LimitReached('integer-arithmetic work cap')

    def fibre(self, n):
        while len(self.fibres) <= n:
            old = self.fibres[-1]
            new = [0]*self.m
            for ai, count in enumerate(old):
                if count:
                    self.tick()
                    x, y = self.next[ai]
                    new[x] += count
                    new[y] += count
            self.fibres.append(tuple(new))
        return self.fibres[n]

    def filter_v(self, e, n):
        key = (e, n)
        if key not in self.filtered:
            f = self.fibre(n)
            out = []
            for indices in self.allowed[e-1]:
                self.tick(len(indices))
                out.append(sum(f[b] for b in indices))
            self.filtered[key] = tuple(out)
        return self.filtered[key]

    def counts(self, n):
        """Return (accepted words, flagged period incidences, difference)."""
        if type(n) is not int or n < 0:
            raise ValueError('Length must be a nonnegative integer')
        I = self.instance
        A = sum(count for action, count in zip(self.actions, self.fibre(n))
                if action[I.start] in I.final)
        B = 0
        for e in range(1, self.k):
            # n=(e+1)*|u| + e*|v|; v must be nonempty.
            for ulen in range((n-e)//(e+1)+1):
                remaining = n-(e+1)*ulen
                if remaining % e:
                    continue
                vlen = remaining//e
                if vlen < 1:
                    continue
                us = self.fibre(ulen)
                vs = self.filter_v(e, vlen)
                self.tick(self.m)
                B += sum(u*v for u, v in zip(us, vs))
        return A, B, A-B


def word_at_length(I, length, max_nodes=200000):
    """Reconstruct only AFTER an exact positive count, checking both predicates."""
    can = [set(I.final)]
    for _ in range(length):
        can.append({q for q, row in enumerate(I.delta) if any(t in can[-1] for t in row)})
    todo = [('', I.start)]
    checked = 0
    while todo:
        w, q = todo.pop()
        checked += 1
        if max_nodes is not None and checked > max_nodes:
            raise LimitReached('witness-reconstruction cap')
        remaining = length-len(w)
        if remaining == 0:
            if witness(I, w):
                assert border_witness(I, w)
                return w, checked
            continue
        for a in (1, 0):
            t = I.delta[q][a]
            if t >= 0 and t in can[remaining-1]:
                todo.append((w+str(a), t))
    raise AssertionError('Positive exact count had no concrete witness')


def solve_one_source_unambiguous(I, max_monoid=10000, max_work=2000000, max_coefficients=20000,
                   max_reconstruction=200000):
    """Decide certified single-source inputs, including EVERY one-flag instance.

    Removing returns to its source is an existence-preserving reduction,
    not a claim that it preserves the full original witness language.
    Every uncapped call terminates. Positive outputs have independently
    checked concrete words; cap failures never become negative answers.
    """
    validate(I)
    for cap in (max_coefficients, max_reconstruction):
        if cap is not None and (type(cap) is not int or cap < 1):
            raise ValueError('Caps must be positive integers or None')
    sources = {p for p, q in I.flags}
    if len(sources) > 1:
        return dict(status='UNKNOWN', reason='Multiple flag sources need joint-incidence counting')
    k = len(I.delta)
    if not I.flags:
        w = shortest_path(I, I.start, I.final, I.bad)
        if w is None:
            return dict(status='NO', reason='No safe accepted path')
        assert witness(I, w) and border_witness(I, w)
        return dict(status='YES', word=w, method='ordinary reachability')
    p = next(iter(sources))
    targets = frozenset(q for a, q in I.flags)
    w = shortest_path(I, I.start, I.final, I.bad | {p})
    if w is not None:
        assert witness(I, w) and border_witness(I, w)
        return dict(status='YES', word=w, method='path avoiding flag source')
    if p in I.bad or p in targets:
        return dict(status='NO', reason='Every candidate visits forbidden/diagonal source')
    head = shortest_path(I, I.start, {p}, I.bad)
    if head is None:
        return dict(status='NO', reason='No safe source path and no source-free accepting path')
    table = tuple(tuple(t if t >= 0 and s not in I.bad and t not in I.bad and t != p else -1
                        for t in row) for s, row in enumerate(I.delta))
    finals = I.final - I.bad - targets
    J = Instance(table, finals, I.flags, start=p)
    ordinary = shortest_path(J, p, finals)
    if ordinary is None:
        return dict(status='NO', reason='No boundary-safe return-free suffix')
    if witness(J, ordinary):
        answer = head+ordinary
        assert witness(I, answer) and border_witness(I, answer)
        return dict(status='YES', word=answer, method='checked shortest safe candidate')
    # Discard targets that cannot occur on a safe source-to-final suffix.
    effective = frozenset(q for q in targets
                          if shortest_path(J, p, {q}) is not None
                          and shortest_path(J, q, finals) is not None)
    for q in effective:
        for t in effective - {q}:
            if shortest_path(J, q, {t}) is not None:
                return dict(status='UNKNOWN', reason='Distinct targets can occur on one path; joint-period counting required')
    try:
        counter = MonoidCounter(J, effective, max_monoid, max_work)
        common = dict(monoid_size=counter.m, suffix_coefficient_bound=counter.bound,
                      full_witness_length_bound=counter.bound+k-2, head=head)
        verified_zero = 0
        for n in range(counter.bound):
            if max_coefficients is not None and n >= max_coefficients:
                return dict(common, status='UNKNOWN', reason='coefficient cap', checked_coefficients=n)
            accepted, incidences, good = counter.counts(n)
            if good < 0:
                raise AssertionError('Unique-period counting produced a negative witness count')
            if good:
                suffix, nodes = word_at_length(J, n, max_reconstruction)
                answer = head+suffix
                assert witness(I, answer) and border_witness(I, answer)
                return dict(common, status='YES', word=answer, method='rational exact counting',
                            first_positive_suffix_length=n, witness_count=good,
                            accepted_count=accepted, period_incidence_count=incidences,
                            checked_coefficients=n+1, work=counter.work, reconstruction_nodes=nodes)
            verified_zero += 1
        return dict(common, status='NO', reason='All coefficients below proved numerator-degree bound vanish',
                    checked_coefficients=verified_zero, work=counter.work)
    except LimitReached as exc:
        return dict(status='UNKNOWN', reason=str(exc))


def solve_one_flag(I, **limits):
    """Complete uncapped decision for at most one ordered forbidden pair."""
    validate(I)
    if len(I.flags) > 1:
        return dict(status='UNKNOWN', reason='More than one flag supplied to one-flag entry point')
    return solve_one_source_unambiguous(I, **limits)

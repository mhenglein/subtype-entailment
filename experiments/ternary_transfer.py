#!/usr/bin/env python3
"""Independent component checks for the ordinary ternary transfer (#72).

No bounded search is used as an entailment decision. This script does not
execute Lean/C029. The all-input reduction is specified in the accompanying
note. Exact regular graph checks and P-automaton saturation are separate from
the subset-pair summary under test. Standard library only.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from itertools import product
import hashlib
import json
from pathlib import Path
import platform
import random
import time
from typing import Any, Iterable

Word = tuple[int, ...]
BASE = "19b06d4fed9da635d9b911f0e908d04e4fc4b099"
SEED = 2026092072


def words(r: int, length: int) -> Iterable[Word]:
    for n in range(length + 1):
        yield from product(range(r), repeat=n)


def prefixes(w: Word) -> list[Word]:
    return [w[:i] for i in range(len(w) + 1)]


@dataclass(frozen=True)
class Instance:
    r: int
    transitions: tuple[tuple[int | None, ...], ...]
    initial: int
    finals: frozenset[int]
    bad: frozenset[int]
    flags: frozenset[tuple[int, int]]

    @property
    def k(self) -> int:
        return len(self.transitions)

    def trace(self, w: Word) -> list[int] | None:
        q = self.initial
        out = [q]
        for a in w:
            q = self.transitions[q][a]
            if q is None:
                return None
            out.append(q)
        return out

    def safe(self, q: int) -> bool:
        return q not in self.bad and (q, q) not in self.flags

    def witness(self, w: Word) -> bool:
        run = self.trace(w)
        if run is None or run[-1] not in self.finals:
            return False
        if any(q in self.bad for q in run):
            return False
        # Literal Basic.Witness; includes diagonals and the empty suffix.
        for j in range(len(w) + 1):
            for i in range(j + 1):
                if w[j:] == w[i:i + len(w) - j]:
                    if (run[i], run[j]) in self.flags:
                        return False
        return True

    def absorbing(self) -> bool:
        for q in self.finals:
            for s in self.transitions[q]:
                if s is not None and (
                    s not in self.finals or any(t == s for _, t in self.flags)
                ):
                    return False
        return True

    def terminalize(self) -> Instance:
        trans = tuple(tuple(s if self.safe(q) and s is not None and self.safe(s)
                            else None for s in row)
                      for q, row in enumerate(self.transitions))
        finals = frozenset(q for q in self.finals if self.safe(q)
                           and all(s is None for s in trans[q]))
        return Instance(self.r, trans, self.initial, finals, self.bad, self.flags)

    def data(self) -> dict[str, Any]:
        return {"r": self.r, "transitions": self.transitions,
                "initial": self.initial, "finals": sorted(self.finals),
                "bad": sorted(self.bad), "flags": sorted(self.flags)}


def codebook(r: int) -> tuple[Word, ...]:
    if r < 1:
        raise ValueError("arity must be positive")
    if r == 1:
        return ((0,),)
    return tuple((1,) * i + (0,) for i in range(r - 1)) + ((1,) * (r - 1),)


def encode_word(r: int, w: Word) -> Word:
    codes = codebook(r)
    return tuple(b for a in w for b in codes[a])


@dataclass
class Coding:
    source: Instance
    target: Instance
    phases: tuple[Word, ...]
    codes: tuple[Word, ...]

    def finish_decode(self, w: Word) -> tuple[Word, Word]:
        """Given a target witness, return a completed word and source witness."""
        if not self.target.witness(w):
            raise ValueError("not a target witness")
        run = self.target.trace(w)
        assert run is not None
        q, pi = divmod(run[-1], len(self.phases))
        p = self.phases[pi]
        suffix: Word = ()
        if p:
            for a, c in enumerate(self.codes):
                s = self.source.transitions[q][a]
                if c[:len(p)] == p and s is not None and self.source.safe(s):
                    suffix = c[len(p):]
                    break
            else:
                raise AssertionError("safe internal witness has no completion")
        complete = w + suffix
        assert self.target.witness(complete)
        decoded: list[int] = []
        pending: Word = ()
        for b in complete:
            pending += (b,)
            if pending in self.codes:
                decoded.append(self.codes.index(pending))
                pending = ()
        assert not pending
        result = tuple(decoded)
        assert self.source.witness(result)
        return complete, result


def encode_instance(i: Instance) -> Coding:
    if not i.absorbing():
        raise ValueError("strong absorption is required")
    codes = codebook(i.r)
    phases = tuple(sorted({c[:j] for c in codes for j in range(len(c))},
                          key=lambda p: (len(p), p)))
    assert phases[0] == ()
    width = len(phases)
    trans: list[tuple[int | None, ...]] = []
    finals: set[int] = set()
    bad: set[int] = set()
    for q in range(i.k):
        for pi, p in enumerate(phases):
            state = q * width + pi
            if q in i.finals:
                finals.add(state)
            if not p:
                if q in i.bad:
                    bad.add(state)
            elif not any(c[:len(p)] == p and i.transitions[q][a] is not None
                         and i.safe(i.transitions[q][a])
                         for a, c in enumerate(codes)):
                bad.add(state)
            row: list[int | None] = []
            for b in range(2):
                pb = p + (b,)
                if pb in phases:
                    row.append(q * width + phases.index(pb))
                elif pb in codes:
                    s = i.transitions[q][codes.index(pb)]
                    row.append(None if s is None else s * width)
                else:
                    row.append(None)
            trans.append(tuple(row))
    flags = frozenset((p * width, q * width) for p, q in i.flags)
    j = Instance(2, tuple(trans), i.initial * width,
                 frozenset(finals), frozenset(bad), flags)
    return Coding(i, j, phases, codes)


@dataclass
class Graph:
    """Finite graph of bottom / one r-ary constructor; cycles are allowed."""
    r: int
    nodes: list[tuple[int, ...] | None]

    def add(self, children: tuple[int, ...]) -> int:
        assert len(children) == self.r
        self.nodes.append(children)
        return len(self.nodes) - 1

    def member(self, root: int, w: Word) -> bool:
        q = root
        for a in w:
            row = self.nodes[q]
            if row is None:
                return False
            q = row[a]
        return self.nodes[q] is not None

    def separator(self, left: int, right: int) -> Word | None:
        """Exact all-depth inclusion check by finite pair reachability."""
        todo = deque([(left, right, ())])
        seen: set[tuple[int, int]] = set()
        while todo:
            p, q, w = todo.popleft()
            if (p, q) in seen:
                continue
            seen.add((p, q))
            a, b = self.nodes[p], self.nodes[q]
            if a is None:
                continue
            if b is None:
                return w
            todo.extend((a[x], b[x], w + (x,)) for x in range(self.r))
        return None

    def eval(self, term: Any, values: dict[str, int]) -> int:
        if term is None:
            return 0
        if isinstance(term, str):
            return values[term]
        return self.add(tuple(self.eval(t, values) for t in term))


@dataclass(frozen=True)
class PDS:
    r: int
    n: int
    eps: frozenset[tuple[int, int]]
    push: frozenset[tuple[int, int, int]]  # (from, letter, to)
    pop: frozenset[tuple[int, int, int]]
    forced: frozenset[int]
    denied: frozenset[int]

    def reverse(self) -> PDS:
        return PDS(self.r, self.n, frozenset((q, p) for p, q in self.eps),
                   frozenset((q, a, p) for p, a, q in self.pop),
                   frozenset((q, a, p) for p, a, q in self.push),
                   frozenset(), frozenset())


def transitive(n: int, edges: Iterable[tuple[int, int]]) -> list[set[int]]:
    out = [{q} for q in range(n)]
    for p, q in edges:
        out[p].add(q)
    for m in range(n):
        for p in range(n):
            if m in out[p]:
                out[p].update(out[m])
    return out


def balanced(w: PDS) -> list[set[int]]:
    e = transitive(w.n, w.eps)
    while True:
        edges = {(p, q) for p in range(w.n) for q in e[p]}
        for p, a, x in w.push:
            for y, b, q in w.pop:
                if a == b and y in e[x]:
                    edges.add((p, q))
        new = transitive(w.n, edges)
        if new == e:
            return e
        e = new


@dataclass
class Summary:
    w: PDS

    def __post_init__(self) -> None:
        self.rev = self.w.reverse()
        self.e = balanced(self.w)
        self.er = balanced(self.rev)
        assert all((q in self.e[p]) == (p in self.er[q])
                   for p in range(self.w.n) for q in range(self.w.n))
        self.roots = self.close(self.w.forced, self.e)
        reverse_edges = {(p, q) for p in range(self.w.n) for q in self.er[p]}
        reverse_edges.update((p, q) for p, _, q in self.rev.pop)
        reach = transitive(self.w.n, reverse_edges)
        self.danger = self.close(self.w.denied, reach)

    @staticmethod
    def close(xs: Iterable[int], e: list[set[int]]) -> frozenset[int]:
        return frozenset(q for p in xs for q in e[p])

    def step(self, xs: Iterable[int], a: int, reverse: bool = False) -> frozenset[int]:
        w, e = (self.rev, self.er) if reverse else (self.w, self.e)
        source = self.close(xs, e)
        return self.close((q for p, b, q in w.pop if b == a and p in source), e)

    def sat(self) -> bool:
        return self.roots.isdisjoint(self.danger)

    def trace(self, left: int, right: int, word: Word) -> list[tuple[frozenset[int], frozenset[int]]]:
        a, b = self.close([left], self.e), self.close([right], self.er)
        out = [(a, b)]
        for c in word:
            a, b = self.step(a, c), self.step(b, c, True)
            out.append((a, b))
        return out

    def witness(self, left: int, right: int, word: Word) -> bool:
        run = self.trace(left, right, word)
        if not run[-1][1].isdisjoint(self.roots):
            return False
        if any(not a.isdisjoint(self.danger) for a, _ in run):
            return False
        for j in range(len(word) + 1):
            for i in range(j + 1):
                if word[j:] == word[i:i + len(word) - j]:
                    if not run[i][0].isdisjoint(run[j][1]):
                        return False
        return True

    def materialize(self, left: int, right: int, limit: int = 256) -> Instance:
        n = self.w.n
        k = 4 ** n
        if k > limit:
            raise ValueError("diagnostic allocation cap, not a negative verdict")
        subsets = [frozenset(x for x in range(n) if m >> x & 1) for m in range(2 ** n)]
        pairs = list(product(subsets, repeat=2))
        index = {p: q for q, p in enumerate(pairs)}
        trans = tuple(tuple(index[(self.step(a, c), self.step(b, c, True))]
                            for c in range(self.w.r)) for a, b in pairs)
        bad = frozenset(q for q, (a, _) in enumerate(pairs) if not a.isdisjoint(self.danger))
        final = frozenset(q for q, (_, b) in enumerate(pairs) if b.isdisjoint(self.roots))
        flags = frozenset((p, q) for p, (a, _) in enumerate(pairs)
                          for q, (_, b) in enumerate(pairs) if not a.isdisjoint(b))
        init = index[(self.close([left], self.e), self.close([right], self.er))]
        return Instance(self.w.r, trans, init, final, bad, flags)


class PostAutomaton:
    """Independent exact Post* saturation, no balanced/Pop summaries.

    Configurations (q,u) are accepted by an epsilon-NFA starting at q.
    eps p->q adds q-epsilon->p, push p-a->q adds q-a->p;
    pop p-a->q copies every epsilon/a/epsilon successor of p to q.
    All added pop-copy edges are epsilon. A finite edge fixed point terminates.
    """
    def __init__(self, w: PDS, seeds: list[tuple[int, Word]]) -> None:
        self.w = w
        self.count = w.n + 1
        self.accept = w.n
        self.eps = {(q, p) for p, q in w.eps}
        self.edges = {(q, a, p) for p, a, q in w.push}
        for p, word in seeds:
            curr = p
            for a in word:
                nxt = self.count
                self.count += 1
                self.edges.add((curr, a, nxt))
                curr = nxt
            self.eps.add((curr, self.accept))
        while True:
            e = transitive(self.count, self.eps)
            added = set(self.eps)
            for p, a, q in w.pop:
                for s, b, t in self.edges:
                    if b == a and s in e[p]:
                        added.update((q, x) for x in e[t])
            if added == self.eps:
                self.e = e
                break
            self.eps = added

    def close(self, states: Iterable[int]) -> frozenset[int]:
        return frozenset(y for x in states for y in self.e[x])

    def step(self, states: frozenset[int], a: int) -> frozenset[int]:
        return self.close(t for s, b, t in self.edges if b == a and s in states)

    def member(self, q: int, word: Word) -> bool:
        states = self.close([q])
        for a in word:
            states = self.step(states, a)
        return self.accept in states

    def nonempty(self, q: int) -> bool:
        edges = set(self.eps) | {(s, t) for s, _, t in self.edges}
        return self.accept in transitive(self.count, edges)[q]

    def graph(self, limit: int = 10000) -> tuple[Graph, list[int]]:
        roots = [self.close([q]) for q in range(self.w.n)]
        todo = deque(roots)
        transitions: dict[frozenset[int], tuple[frozenset[int], ...]] = {}
        while todo:
            s = todo.popleft()
            if s in transitions:
                continue
            if len(transitions) >= limit:
                raise RuntimeError("determinization cap: UNKNOWN, not a decision")
            children = tuple(self.step(s, a) for a in range(self.w.r))
            # Exact prefix-closure verification, not a finite-depth test:
            # a rejecting state may not have an accepting reachable successor.
            if self.accept not in s:
                for x in children:
                    if self.accept in x:
                        raise AssertionError("canonical language not prefix-closed")
            transitions[s] = children
            todo.extend(children)
        accepting = [s for s in transitions if self.accept in s]
        ids = {s: i + 1 for i, s in enumerate(accepting)}
        graph = Graph(self.w.r, [None] + [tuple(ids.get(t, 0) for t in transitions[s])
                                             for s in accepting])
        return graph, [ids.get(s, 0) for s in roots]


@dataclass
class Normal:
    r: int
    n: int
    var_ids: dict[str, int]
    atoms: list[tuple[Any, ...]]
    left: int
    right: int

    def pds(self) -> PDS:
        eps, push, pop, forced, denied = set(), set(), set(), set(), set()
        for atom in self.atoms:
            kind, p, *rest = atom
            if kind == "zero":
                denied.add(p)
            elif kind == "var":
                eps.add((p, rest[0]))
            elif kind == "upper":
                pop.update((p, a, q) for a, q in enumerate(rest[0]))
            elif kind == "lower":
                forced.add(p)
                push.update((q, a, p) for a, q in enumerate(rest[0]))
            else:
                raise AssertionError(kind)
        return PDS(self.r, self.n, frozenset(eps), frozenset(push), frozenset(pop),
                   frozenset(forced), frozenset(denied))

    def models(self, graph: Graph, roots: list[int]) -> bool:
        for atom in self.atoms:
            kind, p, *rest = atom
            if kind == "zero":
                left, right = roots[p], 0
            elif kind == "var":
                left, right = roots[p], roots[rest[0]]
            else:
                cons = graph.add(tuple(roots[q] for q in rest[0]))
                left, right = (roots[p], cons) if kind == "upper" else (cons, roots[p])
            if graph.separator(left, right) is not None:
                return False
        return True


def normalize(r: int, constraints: list[tuple[Any, Any]], left: Any, right: Any) -> Normal:
    vars_: set[str] = set()

    def scan(t: Any) -> None:
        if isinstance(t, str):
            vars_.add(t)
        elif t is not None:
            assert isinstance(t, tuple) and len(t) == r
            for x in t:
                scan(x)

    for a, b in constraints + [(left, right)]:
        scan(a)
        scan(b)
    names = {v: i for i, v in enumerate(sorted(vars_))}
    bottom = len(names)
    atoms: list[tuple[Any, ...]] = [("zero", bottom)]
    count = bottom + 1

    def name(t: Any) -> int:
        nonlocal count
        if t is None:
            return bottom
        if isinstance(t, str):
            return names[t]
        children = tuple(name(x) for x in t)
        q = count
        count += 1
        atoms.extend([("upper", q, children), ("lower", q, children)])
        return q

    for a, b in constraints:
        atoms.append(("var", name(a), name(b)))
    a, b = name(left), name(right)
    return Normal(r, count, names, atoms, a, b)


def canonical(n: Normal, word: Word | None) -> PostAutomaton:
    w = n.pds()
    seeds = [(q, ()) for q in w.forced]
    if word is not None:
        seeds += [(n.left, u) for u in prefixes(word)]
    return PostAutomaton(w, seeds)


def realize(i: Instance) -> Normal:
    if i.r != 2 or any(any(x is not None for x in i.transitions[q]) for q in i.finals):
        raise ValueError("C030 requires binary terminal finals")
    k, b = i.k, 2 * i.k
    atoms: list[tuple[Any, ...]] = [("zero", b)]
    for q in range(k):
        atoms.append(("upper", q, tuple(b if t is None else t for t in i.transitions[q])))
        if q not in i.finals:
            atoms.append(("lower", k + q, tuple(b if t is None else k + t
                                                 for t in i.transitions[q])))
    atoms.extend(("var", p, k + q) for p, q in sorted(i.flags))
    atoms.extend(("zero", q) for q in sorted(i.bad))
    return Normal(2, 2 * k + 1, {}, atoms, i.initial, k + i.initial)


def finite_trees(r: int, depth: int) -> list[frozenset[Word]]:
    if depth == 0:
        return [frozenset()]
    prev = finite_trees(r, depth - 1)
    return [frozenset()] + [frozenset({()} | {(a,) + u for a, child in enumerate(cs) for u in child})
                           for cs in product(prev, repeat=r)]


def ctor(*children: frozenset[Word]) -> frozenset[Word]:
    return frozenset({()} | {(a,) + u for a, child in enumerate(children) for u in child})


def naive(tree: frozenset[Word]) -> frozenset[Word]:
    return frozenset(encode_word(3, u) + p for u in tree for p in [(), (1,)])


def random_absorbing(rng: random.Random, r: int, k: int) -> Instance:
    trans = tuple(tuple(rng.choice([None] + list(range(k))) for _ in range(r)) for _ in range(k))
    final = {q for q in range(k) if rng.randrange(3) == 0}
    while True:
        new = final | {s for q in final for s in trans[q] if s is not None}
        if new == final:
            break
        final = new
    protected = {s for q in final for s in trans[q] if s is not None}
    flags = frozenset((p, q) for p in range(k) for q in range(k)
                      if q not in protected and rng.randrange(5) == 0)
    bad = frozenset(q for q in range(k) if rng.randrange(7) == 0)
    return Instance(r, trans, rng.randrange(k), frozenset(final), bad, flags)


def test_naive() -> dict[str, Any]:
    empty = frozenset()
    m = ctor(empty, empty, empty)
    h = ctor(m, m, m)
    values = finite_trees(3, 2)
    assert all(y <= h and y <= ctor(y, y, y) for y in values)
    y = frozenset([(), (0,), (0, 1)])
    assert y <= naive(h)
    assert not y <= ctor(y, ctor(y, y))
    small = [t for t in finite_trees(2, 3) if len(t) <= 2]
    assert all(t <= ctor(t, ctor(t, t)) for t in small)
    return {"source_models_exhausted": len(values), "binary_nodes": 3,
            "separating_address": [0, 1], "minimal_for_this_instance": True,
            "source_premise": "y <= T(M,M,M), M=T(bottom,bottom,bottom)",
            "source_query": "y <= T(y,y,y)", "binary_value": [[], [0], [0, 1]]}


def test_coding() -> dict[str, Any]:
    rng = random.Random(SEED)
    instances: list[Instance] = []
    for r in range(1, 5):
        for row in product([None, 0], repeat=r):
            for f, b, g in product([False, True], repeat=3):
                i = Instance(r, (row,), 0, frozenset([0] if f else []),
                             frozenset([0] if b else []), frozenset([(0, 0)] if g else []))
                if i.absorbing():
                    instances.append(i)
    instances.extend(random_absorbing(rng, r, k) for r in range(1, 6)
                     for k in range(2, 6) for _ in range(15))
    complete_checks = reverse_checks = target_witnesses = incomplete = 0
    nontruncation = None
    for i in instances:
        coding = encode_instance(i)
        j = coding.target
        assert j.absorbing()
        for w in words(i.r, 4 if i.r <= 3 else 3):
            assert i.witness(w) == j.witness(encode_word(i.r, w))
            complete_checks += 1
        terminal = j.terminalize()
        for w in words(2, 7):
            if terminal.witness(w):
                assert j.witness(w)
            if j.witness(w):
                target_witnesses += 1
                completed, decoded = coding.finish_decode(w)
                if completed != w:
                    incomplete += 1
                    if not i.witness(decoded[:-1]) and nontruncation is None:
                        nontruncation = {"source": i.data(), "partial_binary": w,
                                         "completed_binary": completed, "decoded": decoded}
            reverse_checks += 1
    # Explicit partial-word witness that must be completed, not truncated.
    # Source: 0 --0--> 1(final), 1 --1--> 2(final sink), flag (0,1).
    i = Instance(3, ((1, None, None), (None, 2, None), (None, None, None)),
                 0, frozenset([1, 2]), frozenset(), frozenset([(0, 1)]))
    coding = encode_instance(i)
    partial = (0, 1)
    assert coding.target.witness(partial)
    assert not i.witness((0,))
    complete, decoded = coding.finish_decode(partial)
    assert decoded == (0, 1)
    explicit = {"source": i.data(), "partial_binary": partial,
                "completed_binary": complete, "decoded": decoded}
    # Strong absorption would fail if all intermediate states were nonfinal.
    one = Instance(3, ((0, 0, 0),), 0, frozenset([0]), frozenset(), frozenset())
    j = encode_instance(one).target
    mutated = Instance(2, j.transitions, j.initial, frozenset([0]), j.bad, j.flags)
    assert j.absorbing() and not mutated.absorbing()
    return {"instances": len(instances), "complete_word_comparisons": complete_checks,
            "binary_words_checked": reverse_checks, "binary_witnesses": target_witnesses,
            "partial_witnesses_completed": incomplete,
            "nontruncation_fixture": explicit, "random_nontruncation_found": nontruncation is not None,
            "scope": "all one-state absorbing encodings for arities 1..4; seeded samples for 1..5"}


def test_pds() -> dict[str, Any]:
    rng = random.Random(SEED + 1)
    sat_checks = word_checks = graph_checks = absorption_checks = 0
    for z in range(70):
        n = 1 + z % 3
        r = 1 + z % 4
        atoms: list[tuple[Any, ...]] = []
        for _ in range(z % 7):
            p = rng.randrange(n)
            kind = rng.choice(["upper", "lower", "var", "zero"])
            if kind in ["upper", "lower"]:
                atoms.append((kind, p, tuple(rng.randrange(n) for _ in range(r))))
            elif kind == "var":
                atoms.append((kind, p, rng.randrange(n)))
            else:
                atoms.append((kind, p))
        normal = Normal(r, n, {}, atoms, rng.randrange(n), rng.randrange(n))
        w = normal.pds()
        summary = Summary(w)
        base = canonical(normal, None)
        expected_sat = not any(base.nonempty(q) for q in w.denied)
        assert summary.sat() == expected_sat
        sat_checks += 1
        material = summary.materialize(normal.left, normal.right)
        assert material.absorbing()
        absorption_checks += material.k
        for word in words(r, 3):
            post = canonical(normal, word)
            safe = not any(post.nonempty(q) for q in w.denied)
            expected = safe and not post.member(normal.right, word)
            observed = summary.witness(normal.left, normal.right, word)
            assert (summary.sat() and observed) == expected
            assert material.witness(word) == observed
            if expected:
                graph, roots = post.graph()
                assert normal.models(graph, roots)
                assert graph.member(roots[normal.left], word)
                assert not graph.member(roots[normal.right], word)
                graph_checks += 1
            word_checks += 1
    # Without the SAT guard the witness bridge is deliberately false.
    disconnected = Normal(3, 3, {}, [("lower", 2, (2, 2, 2)), ("zero", 2)], 0, 1)
    ds = Summary(disconnected.pds())
    assert not ds.sat() and ds.witness(0, 1, ())
    assert canonical(disconnected, ()).nonempty(2)
    return {"disconnected_unsat_guard": "PASS", "exact_sat_comparisons": sat_checks, "word_comparisons": word_checks,
            "exact_regular_countermodels_checked": graph_checks,
            "physical_states_checked_for_absorption": absorption_checks,
            "oracles": "independent Post* epsilon-NFA saturation and graph pair reachability"}


def test_realization() -> dict[str, Any]:
    rng = random.Random(SEED + 2)
    instances: list[Instance] = []
    for k in range(1, 5):
        for _ in range(15):
            final = frozenset(q for q in range(k) if rng.randrange(3) == 0)
            trans = tuple(tuple(None if q in final else rng.choice([None] + list(range(k)))
                                for _ in range(2)) for q in range(k))
            flags = frozenset((p, q) for p in range(k) for q in range(k) if rng.randrange(5) == 0)
            bad = frozenset(q for q in range(k) if rng.randrange(6) == 0)
            instances.append(Instance(2, trans, rng.randrange(k), final, bad, flags))
    # End-to-end structural lane: ternary witness -> code -> terminal realization
    # -> exact binary graph -> read back binary separating word -> source decode.
    source = Instance(3, ((1, 1, 1), (None, None, None)),
                      0, frozenset([1]), frozenset(), frozenset())
    coded = encode_instance(source)
    instances.append(coded.target.terminalize())
    comparisons = model_checks = base_checks = decoded_checks = 0
    for i in instances:
        normal = realize(i)
        assert normal.n == 2 * i.k + 1
        base_graph, base_roots = canonical(normal, None).graph()
        assert normal.models(base_graph, base_roots)
        base_checks += 1
        for word in words(2, 4):
            post = canonical(normal, word)
            expected = not any(post.nonempty(q) for q in normal.pds().denied)
            expected = expected and not post.member(normal.right, word)
            assert expected == i.witness(word)
            if expected:
                graph, roots = post.graph()
                assert normal.models(graph, roots)
                assert graph.member(roots[normal.left], word)
                assert not graph.member(roots[normal.right], word)
                model_checks += 1
                if i is instances[-1]:
                    completed, source_word = coded.finish_decode(word)
                    assert completed == word and source.witness(source_word)
                    decoded_checks += 1
            comparisons += 1
    return {"decoded_realized_countermodels": decoded_checks, "terminal_instances": len(instances), "always_sat_graphs": base_checks,
            "word_model_comparisons": comparisons, "exact_countermodels": model_checks,
            "implementation": "independent Python C030 formula, not executed Lean"}


def test_expressions() -> dict[str, Any]:
    # Bottom is node 0; nodes 1,2,3 are infinite spines; 4 is the full tree;
    # 5 is the root-only constructor. Inclusion is tested at ALL depths.
    g = Graph(3, [None, (1, 0, 0), (0, 2, 0), (0, 0, 3), (4, 4, 4), (0, 0, 0)])
    fixtures = [
        ("zero_spine", [("x", ("x", None, None)), (("x", None, None), "x")],
         "x", None, {"x": 1}),
        ("nonroot_zero_spine", [("x", ("x", None, None)), (("x", None, None), "x")],
         "x", (None, None, None), {"x": 1}),
        ("middle_spine", [("x", (None, "x", None)), ((None, "x", None), "x")],
         "x", None, {"x": 2}),
        ("nonroot_middle_spine", [("x", (None, "x", None)), ((None, "x", None), "x")],
         "x", (None, None, None), {"x": 2}),
        ("last_spine", [("x", (None, None, "x")), ((None, None, "x"), "x")],
         "x", None, {"x": 3}),
        ("nonroot_last_spine", [("x", (None, None, "x")), ((None, None, "x"), "x")],
         "x", (None, None, (None, None, None)), {"x": 3}),
        ("full_infinite", [("x", ("x", "x", "x")), (("x", "x", "x"), "x")],
         "x", None, {"x": 4}),
        ("mixed_bottom_and_auxiliary", [("y", None), (("x", "y", None), "z"),
                                       ("z", ("x", None, None))],
         "z", "y", {"x": 1, "y": 0, "z": 1}),
        ("query_only_constructor", [("x", "y")],
         (None, "x", None), "y", {"x": 0, "y": 0}),
    ]
    out = []
    for name, premises, s, t, values in fixtures:
        assert all(g.separator(g.eval(a, values), g.eval(b, values)) is None for a, b in premises)
        word = g.separator(g.eval(s, values), g.eval(t, values))
        assert word is not None
        normal = normalize(3, premises, s, t)
        summary = Summary(normal.pds())
        assert summary.sat() and summary.witness(normal.left, normal.right, word)
        post = canonical(normal, word)
        cg, roots = post.graph()
        assert normal.models(cg, roots)
        restricted = {v: roots[q] for v, q in normal.var_ids.items()}
        assert all(cg.separator(cg.eval(a, restricted), cg.eval(b, restricted)) is None
                   for a, b in premises)
        assert cg.member(cg.eval(s, restricted), word)
        assert not cg.member(cg.eval(t, restricted), word)
        out.append({"fixture": name, "normalized_variables": normal.n,
                    "canonical_graph_nodes": len(cg.nodes), "same_separating_address": word})
    # Finite positive instance is exhaustive because H is an explicit finite bound.
    m = (None, None, None)
    h = (m, m, m)
    normal = normalize(3, [("y", h)], "y", ("y", "y", "y"))
    summary = Summary(normal.pds())
    for word in words(3, 3):
        assert not summary.witness(normal.left, normal.right, word)
    # Mixed inconsistent source: a forced constructor is below bottom.
    unsat = normalize(3, [(m, "x"), ("x", None)], "x", "x")
    assert not Summary(unsat.pds()).sat()
    assert canonical(unsat, None).nonempty(unsat.var_ids["x"])
    return {"exact_infinite_graph_and_expression_cases": out,
            "positive_bounded_source_values": 9, "unsat_mixed_case": "PASS",
            "finite_semantics": "not identified with arbitrary-tree semantics"}



def test_full_pipeline() -> dict[str, Any]:
    """Full carriers and actual output graphs; C029 branches have tiny certificates.

    We do NOT execute C029 or use a cap as a NO answer. For the finite case,
    the initial state is a safe final with no safe outgoing edge, hence no
    nonempty safe run or infinite witness exists. For the infinite case,
    an explicit witness/stem/cycle proves the positive branch.
    """
    m = (None, None, None)
    normal = normalize(3, [("y", m)], "y", None)
    summary = Summary(normal.pds())
    assert summary.sat()
    source = summary.materialize(normal.left, normal.right)
    coding = encode_instance(source)
    j = coding.target
    assert j.witness(())
    assert all(q is None or not j.safe(q) for q in j.transitions[j.initial])
    output = realize(j.terminalize())
    graph, roots = canonical(output, ()).graph()
    assert output.models(graph, roots)
    u = graph.separator(roots[output.left], roots[output.right])
    assert u is not None
    # Explicitly off the naive ternary image: a present root without node 1.
    assert graph.member(roots[output.left], ())
    assert not graph.member(roots[output.left], (1,))
    full, w = coding.finish_decode(u)
    assert full == u
    sg, sr = canonical(normal, w).graph()
    assert normal.models(sg, sr)
    values = {v: sr[q] for v, q in normal.var_ids.items()}
    assert sg.separator(sg.eval("y", values), sg.eval(m, values)) is None
    assert sg.member(sg.eval("y", values), w) and not sg.member(0, w)
    terminal_record = {"source": "y<=T(bottom,bottom,bottom); query y<=bottom",
                       "source_normalized_names": normal.n,
                       "source_full_physical_states": source.k,
                       "binary_full_physical_states": j.k,
                       "output_variables": output.n, "output_constraints": len(output.atoms),
                       "exact_output_graph_nodes": len(graph.nodes),
                       "off_image_left_root": True, "decoded_separating_word": w,
                       "negative_infinite_branch_certificate": "safe initial sink"}
    # Positive C029 branch, with a literal safe lasso instead of a C029 run.
    infinite = normalize(3, [], "x", None)
    ii = Summary(infinite.pds()).materialize(infinite.left, infinite.right)
    cc = encode_instance(ii)
    jj = cc.target
    assert jj.witness(())
    q = jj.transitions[jj.initial][0]
    assert q is not None and jj.safe(jj.initial) and jj.safe(q)
    assert jj.transitions[q][0] == q
    _, sw = cc.finish_decode(())
    ig, ir = canonical(infinite, sw).graph()
    assert infinite.models(ig, ir)
    assert ig.member(ir[infinite.left], sw) and not ig.member(ir[infinite.right], sw)
    fixed = Graph(2, [None, (0, 0)])
    assert fixed.separator(1, 0) == ()
    # Source inconsistency selects an inconsistent binary output, not a SAT one.
    inconsistent = normalize(3, [(m, "x"), ("x", None)], "x", None)
    assert not Summary(inconsistent.pds()).sat()
    binary_inconsistent = normalize(2, [((None, None), None)], None, None)
    assert not Summary(binary_inconsistent.pds()).sat()
    return {"terminal_branch": terminal_record,
            "positive_infinite_branch_certificate": {"witness": [], "stem": [0], "cycle": [0]},
            "inconsistent_branch": "PASS",
            "boundary": "C029 results certified for these fixtures; actual C029 executable NOT RUN"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("results/ternary-transfer.json"))
    args = parser.parse_args()
    start = time.monotonic()
    result: dict[str, Any] = {
        "upstream_base": BASE, "seed": SEED, "python": platform.python_version(),
        "platform": platform.platform(),
        "evidence": "bounded component regressions plus exact finite-graph/NFA checks",
        "preserved_failed_attempts": [
            "Naive homomorphic type encoding refuted by a three-node off-image model.",
            "An initial nontruncation TEST FIXTURE used partial word 101; literal Witness correctly rejected it. Repaired fixture uses 01 and completes to 010; encoding algorithm unchanged.",
            "Unconditional summary/model equivalence is invalid without source SAT. A disconnected forced denial regression explicitly preserves this guard."
        ],
        "not_run": ["Lean build", "Lean kernel replay", "C029 executable",
                    "complete source-to-target command-line translator", "independent mathematical review"],
        "naive_counterexample": test_naive(),
        "coding": test_coding(),
        "summary_vs_independent_post": test_pds(),
        "terminal_realization": test_realization(),
        "expressions": test_expressions(),
        "full_pipeline_fixtures": test_full_pipeline(),
    }
    result["elapsed_seconds"] = round(time.monotonic() - start, 3)
    result["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["status"] = "PASS"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Independent, bounded falsification of the #69 compiler-only construction.

This is NOT execution of Lean, NOT a shortest-witness search, and NOT an
exhaustion of the existing enormous diagram union. It independently constructs
literal prefix graphs, removes product-node cycles by BFS, counts fresh blocks,
and reconstructs one common extension from synchronized interval products.
Optional --repository also compares certificates with the unchanged Python
compiler, using its own data types and finite query evaluator.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from itertools import product
import json
import hashlib
from math import prod
from pathlib import Path
import random
from typing import Callable

SOURCE = '19b06d4fed9da635d9b911f0e908d04e4fc4b099'
SEED = 2026092069
LABELS = ('F', 'S', 'K0', 'K1')


@dataclass(frozen=True)
class Instance:
    delta: tuple[tuple[int | None, int | None], ...]
    final: frozenset[int]
    bad: frozenset[int] = frozenset()
    flags: frozenset[tuple[int, int]] = frozenset()

    @property
    def k(self) -> int:
        return len(self.delta)


@dataclass(frozen=True)
class Reference:
    word: str
    labels: tuple[int, ...]


@dataclass(frozen=True)
class Colour:
    state: int
    forbidden: int
    next_bit: str
    root: bool
    end: bool


def border_lengths(w: str) -> tuple[int, ...]:
    return tuple(j for j in range(len(w) + 1) if w[:j] == w[len(w)-j:])


def first_return(b: str, c: str) -> bool:
    m, n = len(b), len(c)
    return bool(m and n > m and c.startswith(b) and c.endswith(b)
                and all(c[j-m:j] != b for j in range(m + 1, n)))


def safe(i: Instance, r: Reference) -> bool:
    n = len(r.word)
    if not n or len(r.labels) != n + 1 or r.labels[0] not in i.final:
        return False
    if any(q < 0 or q >= i.k or q in i.bad for q in r.labels):
        return False
    if any(i.delta[r.labels[j+1]][int(bit)] != r.labels[j]
           for j, bit in enumerate(r.word)):
        return False
    # Direct ordered-flag test, not imported masks or the source checker.
    return all((r.labels[j], r.labels[h]) not in i.flags
               for j in range(n + 1) for h in border_lengths(r.word[:j]))


class Graph:
    def __init__(self, i: Instance, r: Reference):
        self.instance, self.ref = i, r
        self.n = len(r.word)
        self.colours = []
        for j in range(self.n + 1):
            mask = sum(1 << p for p in range(i.k)
                       if any((p, r.labels[h]) in i.flags
                              for h in border_lengths(r.word[:j])))
            self.colours.append(Colour(r.labels[j], mask,
                                      r.word[j:j+1], j == 0, j == self.n))
        self.edges = {}
        for j in range(self.n + 1):
            self.edges[j, 'F'] = max((h for h in border_lengths(r.word[:j])
                                      if h < j), default=0)
            if j < self.n:
                self.edges[j, 'S'] = j + 1
            for bit in '01':
                text = r.word[:j] + bit
                self.edges[j, 'K'+bit] = max(h for h in range(self.n + 1)
                                            if text.endswith(r.word[:h]))

    def edge(self, x: int, label: str) -> int | None:
        return self.edges.get((x, label))

    def outgoing(self, x: int):
        return tuple((label, self.edges[x, label]) for label in LABELS
                     if (x, label) in self.edges)


def guard_holds(guard: tuple[tuple[str, object], ...], c: Colour) -> bool:
    return all((not (c.forbidden >> int(value) & 1)) if field == 'clear'
               else getattr(c, field) == value for field, value in guard)


@dataclass(frozen=True)
class Observer:
    size: int
    initial: tuple[int, ...]
    final: frozenset[int]
    transitions: tuple[tuple[int, str, int], ...]
    guards: tuple[tuple[tuple[str, object], ...], ...]

    def allows(self, q: int, c: Colour) -> bool:
        return 0 <= q < self.size and guard_holds(self.guards[q], c)

    def move(self, q: int, label: str, c: Colour, d: Colour) -> tuple[int, ...]:
        return tuple(sorted({p for s, lab, p in self.transitions
                             if s == q and lab == label and self.allows(p, d)}))


def exact(labels: tuple[str, ...], guards=None) -> Observer:
    s = len(labels) + 1
    return Observer(s, (0,), frozenset({s-1}),
                    tuple((j, lab, j+1) for j, lab in enumerate(labels)),
                    tuple(guards) if guards is not None else ((),)*s)


def loop(labels=LABELS, size=1) -> Observer:
    return Observer(size, (0,), frozenset({0}),
                    tuple((q, lab, p) for q in range(size) for lab in labels
                          for p in range(size)), ((),)*size)


@dataclass(frozen=True)
class Atom:
    observer: Observer
    source: str
    target: str


@dataclass(frozen=True)
class Query:
    variables: tuple[str, ...]
    atoms: tuple[Atom, ...] = ()
    tests: tuple[tuple[str, tuple[tuple[str, object], ...]], ...] = ()
    equal: tuple[tuple[str, str], ...] = ()
    unequal: tuple[tuple[str, str], ...] = ()

    @property
    def weight(self) -> int:
        return max(2, 1 + len(self.variables) + len(self.atoms)
                   + sum(a.observer.size for a in self.atoms))


@dataclass(frozen=True)
class PathWitness:
    nodes: tuple[tuple[int, int], ...]
    labels: tuple[str, ...]


def path(g: Graph, o: Observer, u: int, v: int) -> PathWitness | None:
    todo = deque()
    parent = {}
    for q in o.initial:
        if o.allows(q, g.colours[u]):
            parent[u, q] = None
            todo.append((u, q))
    while todo:
        node = todo.popleft()
        x, q = node
        if x == v and q in o.final:
            nodes, labels = [node], []
            while parent[node] is not None:
                old, label = parent[node]
                labels.append(label)
                nodes.append(old)
                node = old
            return PathWitness(tuple(reversed(nodes)), tuple(reversed(labels)))
        for label, y in g.outgoing(x):
            for p in o.move(q, label, g.colours[x], g.colours[y]):
                nxt = (y, p)
                if nxt not in parent:
                    parent[nxt] = (node, label)
                    todo.append(nxt)
    return None


def relation_oracle(g: Graph, o: Observer) -> set[tuple[int, int]]:
    """Independent Warshall transitive closure, including allowed empty paths."""
    nodes = [(v, q) for v in range(g.n+1) for q in range(o.size)
             if o.allows(q, g.colours[v])]
    ix = {n: j for j, n in enumerate(nodes)}
    rows = [1 << j for j in range(len(nodes))]
    for j, (v, q) in enumerate(nodes):
        for label, w in g.outgoing(v):
            for p in o.move(q, label, g.colours[v], g.colours[w]):
                rows[j] |= 1 << ix[w, p]
    for h in range(len(nodes)):
        for j in range(len(nodes)):
            if rows[j] >> h & 1:
                rows[j] |= rows[h]
    return {(u, v) for u in range(g.n+1) for v in range(g.n+1)
            if any((u, q) in ix and (v, p) in ix
                   and rows[ix[u, q]] >> ix[v, p] & 1
                   for q in o.initial for p in o.final)}


def model_at(g: Graph, query: Query, sigma: dict[str, int]):
    if not all(guard_holds(test, g.colours[sigma[x]]) for x, test in query.tests):
        return None
    if not all(sigma[x] == sigma[y] for x, y in query.equal):
        return None
    if not all(sigma[x] != sigma[y] for x, y in query.unequal):
        return None
    paths = tuple(path(g, a.observer, sigma[a.source], sigma[a.target])
                  for a in query.atoms)
    return None if any(p is None for p in paths) else paths


def segments(p: PathWitness, m: int) -> tuple[tuple[tuple[int, int], ...], ...]:
    blocks = [[p.nodes[0]]]
    for u, v in zip(p.nodes, p.nodes[1:]):
        compatible = (u[0] <= m and v[0] <= m) or (u[0] > m and v[0] == u[0]+1)
        if compatible:
            blocks[-1].append(v)
        else:
            blocks.append([v])
    return tuple(tuple(b) for b in blocks)


def fresh_colour(i: Instance, q: int, bit: str, c: Colour) -> Colour:
    column = sum(1 << p for p in range(i.k) if (p, q) in i.flags)
    return Colour(q, c.forbidden | column, bit, False, bit == '')


def interval_path(i: Instance, b: Reference, active,
                  left: tuple[int, int, str], right: tuple[int, int, str],
                  *, require_positive: bool = True):
    """Exact reachable-state BFS for ONE synchronized interval (all lengths).

    The emitted word, actual state and delayed next bit are shared by every
    coordinate. No cartesian product of independent word-existence answers.
    """
    g = Graph(i, b)
    u, ql, nl = left
    v, qr, nr = right
    start = (u, ql, nl, False, tuple(x[1] for x in active))
    targets = tuple(x[2] for x in active)

    def allowed(node):
        cursor, real, nxt, _, controls = node
        c = g.colours[cursor]
        if real in i.bad or (real, real) in i.flags or c.forbidden >> real & 1:
            return False
        if (nxt == '') != c.end:
            return False
        fc = fresh_colour(i, real, nxt, c)
        return all(o.allows(t, fc) for (o, _, _), t in zip(active, controls))

    if not allowed(start):
        return None
    todo, parent = deque([start]), {start: None}
    while todo:
        node = todo.popleft()
        cursor, real, nxt, seen, controls = node
        if (cursor, real, nxt) == (v, qr, nr) and controls == targets and (seen or not require_positive):
            trace = []
            while parent[node] is not None:
                old, bit = parent[node]
                trace.append((bit, node[1]))
                node = old
            return tuple(reversed(trace))
        if nxt == '' or cursor == g.n:
            continue
        destination = g.edge(cursor, 'K'+nxt)
        assert destination is not None
        for p, row in enumerate(i.delta):
            if row[int(nxt)] != real:
                continue
            for nb in (('',) if destination == g.n else ('0', '1')):
                c = fresh_colour(i, real, nxt, g.colours[cursor])
                d = fresh_colour(i, p, nb, g.colours[destination])
                choices = [tuple(sorted(set(o.move(t, 'S', c, d)) |
                                       set(o.move(t, 'K'+nxt, c, d))))
                           for (o, _, _), t in zip(active, controls)]
                for ts in product(*choices):
                    target = (destination, p, nb, True, ts)
                    if target not in parent and allowed(target):
                        parent[target] = (node, nxt)
                        todo.append(target)
    return None


def chain_instance(word: str) -> tuple[Instance, Reference]:
    rows = [[None, None] for _ in range(len(word)+1)]
    for j, bit in enumerate(word):
        rows[j+1][int(bit)] = j
    i = Instance(tuple(tuple(row) for row in rows), frozenset({0}))
    return i, Reference(word, tuple(range(len(word)+1)))


def compact_forward_counts(sizes, counts) -> bool:
    """A sufficient stronger filter; the final compiler uses compact_intervals."""
    return len(sizes) == len(counts) and all(n <= s+1 for s, n in zip(sizes, counts))


def compact_intervals(sizes, coordinate_counts) -> bool:
    """Final guard: retain all coordinates, but bound their count per interval."""
    budget = len(sizes) + sum(sizes)
    return all(count <= budget for count in coordinate_counts)


def check_certificate(i, b, c, query, sigma, counters, *, repository=False):
    assert safe(i, b) and safe(i, c) and first_return(b.word, c.word)
    gc, gb = Graph(i, c), Graph(i, b)
    paths = model_at(gc, query, sigma)
    assert paths is not None
    m, n = len(b.word), len(c.word)
    bs = tuple(segments(p, m) for p in paths)
    fresh = tuple(tuple(block for block in blocks if block[0][0] > m) for blocks in bs)
    sizes = tuple(a.observer.size for a in query.atoms)
    counts = tuple(len(blocks) for blocks in fresh)
    assert compact_forward_counts(sizes, counts)
    for a, p, blocks in zip(query.atoms, paths, fresh):
        assert len(p.nodes) == len(set(p.nodes))
        assert sum(v == m+1 for v, _ in p.nodes) <= a.observer.size
        assert all(block[0][0] == m+1 for block in blocks[1:])
    marks = sorted({m+1, n} | {p for p in sigma.values() if p > m}
                   | {x[0] for blocks in fresh for block in blocks for x in (block[0], block[-1])})
    cursor = {p: gc.edge(p, 'F') for p in marks}
    for p in marks:
        assert gc.colours[p] == fresh_colour(i, c.labels[p], c.word[p:p+1], gb.colours[cursor[p]])
    total_blocks = sum(map(len, bs))
    v, a, s = len(query.variables), len(query.atoms), sum(sizes)
    t = query.weight
    B, G, M = 3*a+2*s, 2+v+2*a+2*s, 2*a*(3*a+2*s)
    core_vars = v+2*a*total_blocks
    piece_count = sum(2*len(blocks)-1 for blocks in bs)
    assert total_blocks <= B and len(marks) <= G and piece_count <= M
    assert core_vars <= v+M
    ordinary_sizes = []
    for atm, p, blocks in zip(query.atoms, paths, bs):
        ordinary_sizes += [atm.observer.size for block in blocks if block[0][0] <= m]
        for j, (x, y) in enumerate(zip(p.nodes, p.nodes[1:])):
            if x[0] > m >= y[0] and p.labels[j].startswith('K'):
                ordinary_sizes.append(2)
    interval_sizes, reconstructed_trace = [], []
    new_marks = [m+1]
    for lo, hi in zip(marks, marks[1:]):
        active, atom_indices = [], []
        for ai, (atm, blocks) in enumerate(zip(query.atoms, fresh)):
            for block in blocks:
                if block[0][0] <= lo < hi <= block[-1][0]:
                    controls = dict(block)
                    active.append((atm.observer, controls[lo], controls[hi]))
                    atom_indices.append(ai)
                    counters['interior_seam_positions'] += int(block[0][0] < lo) + int(hi < block[-1][0])
        assert compact_intervals(sizes, (len(active),))
        assert len(active) <= s+a <= t-1
        for ai, count in Counter(atom_indices).items():
            assert count <= sizes[ai]+1
        interval_sizes.append(6*i.k*prod(o.size for o, _, _ in active))
        assert interval_sizes[-1] <= 6*i.k*t**(t-1)
        out = interval_path(i, b, active,
                            (cursor[lo], c.labels[lo], c.word[lo:lo+1]),
                            (cursor[hi], c.labels[hi], c.word[hi:hi+1]))
        assert out is not None and len(out) > 0
        reconstructed_trace.extend(out)
        new_marks.append(m+1+len(reconstructed_trace))
        counters['shared_intervals'] += int(len(active) > 1)
        counters['repeated_observer_intervals'] += int(any(vv > 1 for vv in Counter(atom_indices).values()))
        counters['intervals'] += 1
    output_weight = max(2, 1+(2+len(marks)+core_vars)
                        +(2+len(ordinary_sizes)+len(interval_sizes))
                        +4+sum(ordinary_sizes)+sum(interval_sizes))
    envelope = 8+5*t+12*t*t+6*t**3+12*i.k*t**t
    assert output_weight <= envelope <= 28*i.k*t**(t+1) <= 64*i.k*t**(2*t+2)
    generated = Reference(b.word+c.word[m]+''.join(bit for bit, _ in reconstructed_trace),
                          b.labels+(c.labels[m+1],)+tuple(q for _, q in reconstructed_trace))
    assert safe(i, generated) and first_return(b.word, generated.word)
    role_map = dict(zip(marks, new_marks))
    sigma2 = {x: (role_map[p] if p > m else p) for x, p in sigma.items()}
    assert model_at(Graph(i, generated), query, sigma2) is not None
    counters['certificates'] += 1
    counters['changed_length_reconstructions'] += int(len(generated.word) != n)
    counters['overlapping_returns'] += int(n-m < m)
    counters['coincident_first_last'] += int(m+1 == n)
    counters['fresh_zero_blocks'] += sum(len(block) == 1 for blocks in fresh for block in blocks)
    counters['old_zero_blocks'] += sum(len(block) == 1 and block[0][0] <= m for blocks in bs for block in blocks)
    counters['distinct_marks_same_origin'] += int(len(set(cursor.values())) < len(marks))
    counters['coincident_variable_roles'] += int(len(set(sigma.values())) < len(sigma))
    counters['multiple_atom_conjunctions'] += int(a >= 2)
    if repository:
        repository_compare(i, b, c, query, sigma, paths, counters)
    return generated, output_weight


def repository_compare(i, b, c, query, sigma, paths, counters):
    """Actual unchanged Python compiler: certificate comparison, NOT Lean."""
    from rank_preimage_core import Atom as A, Query as Q, Model, Test, table, TRUE, model
    from rank_preimage import extract_diagram, compile_diagram
    from rank_query_graphs import Reference as R, graph_from_reference
    from types import SimpleNamespace
    original_i = SimpleNamespace(delta=i.delta, final=i.final, bad=i.bad, flags=i.flags)

    def test(g):
        ts = tuple(Test('clear', ('forbidden', value)) if field == 'clear'
                   else Test('field', (field, value)) for field, value in g)
        return Test('and', ts) if ts else TRUE

    obs = [table(a.observer.size, a.observer.transitions, a.observer.initial,
                 a.observer.final, tuple(test(g) for g in a.observer.guards)) for a in query.atoms]
    q = Q(query.variables, tuple((x, test(g)) for x, g in query.tests), query.equal,
          query.unequal, tuple(A(o, a.source, a.target) for o, a in zip(obs, query.atoms)))
    converted = tuple((p.nodes[0][1], tuple((u[0], u[1], lab, v[0], v[1])
                      for u, lab, v in zip(p.nodes, p.labels, p.nodes[1:]))) for p in paths)
    B, C = R(b.word, b.labels), R(c.word, c.labels)
    diagram = extract_diagram(original_i, B, C, q, Model(dict(sigma), converted))
    counts = tuple(sum(p.kind == 'forward' for p in ps) for ps in diagram.pieces)
    assert compact_forward_counts(tuple(o.size for o in obs), counts)
    group_index = {name: j for j, group in enumerate(diagram.groups) for name in group}
    active_counts = [sum(piece.kind == "forward" and
                         group_index[piece.source] <= j < group_index[piece.target]
                         for pieces in diagram.pieces for piece in pieces)
                     for j in range(len(diagram.groups)-1)]
    assert compact_intervals(tuple(o.size for o in obs), active_counts)
    compiled = compile_diagram(original_i, q, diagram)
    assert max(2, compiled.weight) <= 64*i.k*max(2, q.weight)**(2*max(2, q.weight)+2)
    assert model(graph_from_reference(original_i, B), compiled) is not None
    counters['unchanged_python_compiler_certificates'] += 1


def run(repository=False):
    if repository:
        source_files = {
            'rank_preimage.py': '852fa7d7ba199b9d91ab24a8f7b5abf29ed8819b',
            'rank_preimage_core.py': 'fe297ab4f2252468b1734f6885765cde0d2cecb9',
            'rank_query_graphs.py': '6fcc612e47ef65edbb7ec9ff973a528a422da8e4',
            'rank_query_prefix.py': '135d3cb960d07dfddefd74dd255bba289a08af1b',
        }
        for name, expected in source_files.items():
            data = Path(__file__).with_name(name).read_bytes()
            actual = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            if actual != expected:
                raise RuntimeError('Pinned source mismatch: '+name+' '+actual)
    rng = random.Random(SEED)
    counters = Counter()
    boundary = {}
    # All binary first-return word pairs through six letters, with exact
    # acyclic terminal labellings, including overlaps and one-letter returns.
    pairs = []
    for n in range(2, 7):
        for bits in product('01', repeat=n):
            w = ''.join(bits)
            for m in range(1, n):
                if first_return(w[:m], w):
                    pairs.append((w[:m], w))
    for bword, cword in pairs:
        i, c = chain_instance(cword)
        b = Reference(bword, c.labels[:len(bword)+1])
        g = Graph(i, c)
        # Literal BFS is independently checked by full finite relation closure.
        o = loop(tuple(l for l in LABELS if rng.randrange(2)), 1 + rng.randrange(2))
        oracle = relation_oracle(g, o)
        for u in range(g.n+1):
            for v in range(g.n+1):
                assert ((path(g, o, u, v) is not None) == ((u, v) in oracle))
                counters['path_relation_comparisons'] += 1
        for trial in range(3):
            sigma = {'x': rng.randrange(g.n+1), 'e': g.n}
            atoms = []
            for ai in range(2):
                nodes, labs = [sigma['x']], []
                for _ in range(rng.randrange(9)):
                    label, dest = rng.choice(g.outgoing(nodes[-1]))
                    nodes.append(dest)
                    labs.append(label)
                guards = []
                for p in nodes:
                    col = g.colours[p]
                    field = rng.choice(('state', 'next_bit', 'root', 'end'))
                    guards.append(((field, getattr(col, field)),) if trial == 2 else ())
                name = 'u'+str(ai)
                sigma[name] = nodes[-1]
                atoms.append(Atom(exact(tuple(labs), guards), 'x', name))
            pair = (('u0', 'u1'),)
            q = Query(('x', 'u0', 'u1', 'e'), tuple(atoms), (('e', (('end', True),)),),
                      pair if sigma['u0'] == sigma['u1'] else (),
                      () if sigma['u0'] == sigma['u1'] else pair)
            check_certificate(i, b, c, q, sigma, counters,
                              repository=repository and counters['certificates'] < 36)
    counters['binary_first_return_pairs_through_length_6'] = len(pairs)
    # One real observer must traverse the SAME fresh interval twice, with
    # different control pairs. A once-only pruning is incomplete here.
    i, c = chain_instance('0101')
    b = Reference('01', c.labels[:3])
    o = exact(('S', 'K0', 'S'))
    q = Query(('x', 'y'), (Atom(o, 'x', 'y'),),
              (('x', (('state', 3),)), ('y', (('end', True),))))
    check_certificate(i, b, c, q, {'x': 3, 'y': 4}, counters, repository=repository)
    p = path(Graph(i, c), o, 3, 4)
    fresh_count = sum(block[0][0] > 2 for block in segments(p, 2))
    assert fresh_count == 2 and fresh_count > 1 and fresh_count <= o.size+1
    boundary['once_only_filter_counterexample'] = {'word': '0101', 'path': ['S', 'K0', 'S'],
                                                   'required_forward_blocks': fresh_count}
    # Actual terminal instance with unbounded reverse references 0 1^r 0.
    i = Instance(((None, None), (0, 1), (1, 2)), frozenset({0}))
    b = Reference('0', (0, 1))
    o2, o3 = exact(('S', 'S')), exact(('S', 'S', 'S'))
    left, right = (0, 1, '1'), (1, 2, '')
    two = interval_path(i, b, [(o2, 0, 2)], left, right)
    three = interval_path(i, b, [(o3, 0, 3)], left, right)
    joint = interval_path(i, b, [(o2, 0, 2), (o3, 0, 3)], left, right)
    duplicate = interval_path(i, b, [(o2, 0, 2), (o2, 0, 2)], left, right)
    assert two is not None and three is not None and joint is None and duplicate is not None
    boundary['shared_generator_conflict'] = {'individual_words': [''.join(x[0] for x in two),
                                                                 ''.join(x[0] for x in three)],
                                            'joint': False, 'duplicate_same_observation': True,
                                            'oracle': 'exact finite product reachability, all lengths'}
    for r in range(1, 9):
        c = Reference('0'+'1'*r+'0', (0,)+(1,)*(r+1)+(2,))
        # next=1 at the first fresh mark when r>=2; loops permit shorter
        # synchronized reconstructions, not only replay of the supplied C.
        sigma = {'x': 2, 'e': len(c.word), 'same': 2}
        q = Query(('x', 'e', 'same'), (Atom(loop(('S',)), 'x', 'e'),
                   Atom(loop(('S',)), 'same', 'e')), (('e', (('end', True),)),), (('x', 'same'),))
        check_certificate(i, b, c, q, sigma, counters, repository=repository)
    # No positive physical interval may be collapsed merely because both
    # marks have the same KMP origin, state, and delayed next bit.
    empty = exact(())
    self_left = (0, 1, '1')
    assert interval_path(i, b, [(empty, 0, 0)], self_left, self_left) is None
    assert interval_path(i, b, [(empty, 0, 0)], self_left, self_left, require_positive=False) == ()
    boundary['zero_length_interval_mutant_rejected'] = True
    # No path atoms: the shared generator must still exist. One fresh vertex
    # means coincident first/last marks, not a positive empty interval.
    for word in ('00', '000'):
        ii, cc = chain_instance(word)
        bb = Reference(word[:-1], cc.labels[:-1])
        check_certificate(ii, bb, cc, Query(()), {}, counters, repository=repository)
    ii, cc = chain_instance('000')
    bb = Reference('00', cc.labels[:3])
    q = Query(('x', 'y'), (Atom(empty, 'x', 'y'),), (), (('x', 'y'),))
    check_certificate(ii, bb, cc, q, {'x': 3, 'y': 3}, counters, repository=repository)
    zero = Observer(0, (), frozenset(), (), ())
    assert path(Graph(ii, cc), zero, 0, 0) is None
    boundary['zero_state_observer_unsatisfiable'] = True
    boundary['empty_query_union_output'] = []
    # Flags: exact diagonal, ordered and empty-border tests, including safety
    # rejection at the empty border. Reconstruct every retained safe example.
    base_i, cc = chain_instance('0101')
    bb = Reference('01', cc.labels[:3])
    flags_seen = {'safe': 0, 'unsafe': 0}
    for flag in product(range(base_i.k), repeat=2):
        ii = Instance(base_i.delta, base_i.final, flags=frozenset({flag}))
        if safe(ii, cc) and safe(ii, bb):
            q = Query(('x', 'e'), (Atom(loop(('S',)), 'x', 'e'),), (('e', (('end', True),)),))
            check_certificate(ii, bb, cc, q, {'x': 3, 'e': 4}, counters,
                              repository=repository)
            flags_seen['safe'] += 1
        else:
            flags_seen['unsafe'] += 1
    boundary['ordered_flag_cases'] = flags_seen
    assert not safe(Instance(base_i.delta, base_i.final, flags=frozenset({(4, 0)})), cc)
    boundary['empty_border_flag_rejected'] = True
    assert not safe(Instance(base_i.delta, base_i.final, bad=frozenset({3})), cc)
    boundary['bad_state_rejected'] = True
    # Preserved #47 arithmetic; do not enumerate its 2^175 product states.
    old_weight, target = 12+30*2**175, 320*17**36
    assert old_weight > target
    assert not compact_intervals((2,)*5, (175,))
    assert compact_intervals((2,)*5, (5,))
    assert not compact_forward_counts((2,)*5, (35,)*5)
    assert compact_forward_counts((2,)*5, (1,)*5)
    if repository:
        from rank_preimage_core import Atom as A, Query as Q, table, model
        from rank_preimage import Diagram as D, Piece as P, compile_diagram
        from rank_query_graphs import Reference as R, graph_from_reference
        from types import SimpleNamespace
        original_i = SimpleNamespace(delta=base_i.delta, final=base_i.final,
                                     bad=base_i.bad, flags=base_i.flags)
        old_obs = table(2, tuple((q, lab, p) for q in range(2) for lab in LABELS
                               for p in range(2)), (0,), (0,))
        old_query = Q(('x',), atoms=(A(old_obs, 'x', 'x'),)*5)
        base_graph = graph_from_reference(original_i, R('01', (0, 1, 2)))
        forward = P('forward', 'x0', 'x1', 0, 0)
        wrap = P('wrap', 'x1', 'x0', 0, 0, 'K0')
        def diagram(repeats):
            return D((('x', 'fresh', 'x0'),), (('x0', '@first'), ('x1', '@last')),
                     (3, 4), ('1', ''), '0', base_graph.colours[2],
                     ((forward, wrap)*repeats,)*5)
        assert compile_diagram(original_i, old_query, diagram(35)).weight == old_weight
        small = compile_diagram(original_i, old_query, diagram(1))
        assert small.weight == 12+30*2**5
        assert model(base_graph, small) is not None
        counters['unchanged_python_counterexample_replays'] += 1
    boundary['preserved_counterexample'] = {'input_weight': 17, 'old_output_weight': str(old_weight),
                                          'original_target': str(target), 'old_diagram_filtered': True,
                                          'retained_coordinate_cap': 15, 'rejected_coordinate_count': 175,
                                          'smaller_coordinate_count': 5, 'smaller_output_weight': 972}
    # Independent integer check of the full conservative resource envelope.
    # Enumeration is over aggregate input parameters, not graph witnesses.
    for v in range(9):
        for a in range(9):
            for s in range(25):
                t = max(2, 1+v+a+s)
                M, n, nc = 2*a*(3*a+2*s), 2+v+2*a+2*s, v+2*a*(3*a+2*s)
                for k in (1, 2, 5, 17):
                    raw = 8+2*n+nc+(1+t)*M+(n-1)*6*k*t**(s+a)
                    poly = 8+5*t+12*t*t+6*t**3+12*k*t**t
                    assert raw <= poly <= 28*k*t**(t+1) <= 64*k*t**(2*t+2)
                    counters['integer_envelope_checks'] += 1
    required = ('shared_intervals', 'repeated_observer_intervals', 'interior_seam_positions',
                'changed_length_reconstructions', 'overlapping_returns', 'coincident_first_last',
                'fresh_zero_blocks', 'old_zero_blocks', 'distinct_marks_same_origin',
                'coincident_variable_roles', 'multiple_atom_conjunctions')
    assert all(counters[key] > 0 for key in required)
    return {'status': 'PASS', 'source_revision': SOURCE, 'seed': SEED,
            'evidence': 'Independent finite corpus; complete finite interval-product oracles; exact integer arithmetic.',
            'limits': ['Not a full enumeration of all bounded diagrams.', 'Not a Lean execution.',
                       'No shortest-witness F claim.', 'No human or separate-agent review implied.'],
            'repository_comparison': 'RUN' if repository else 'NOT RUN',
            'counts': dict(sorted(counters.items())), 'boundaries': boundary}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--repository', action='store_true')
    args = parser.parse_args()
    result = run(args.repository)
    text = json.dumps(result, sort_keys=True, indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()

"""Exact prefix graphs and walk-guided first-return extensions.

Research kernel for a candidate unrestricted query-elimination proof.
This file is NOT an unrestricted existence solver or the full query compiler.
All graph/query operations here are finite and independently testable.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable, Optional
from border_lab import Instance, witness, border_witness
from rank_query_prefix import Reference, prefix_function, border_chain, valid_reverse_prefix

EDGE_LABELS = ('F', 'S', 'K0', 'K1')


@dataclass(frozen=True)
class Colour:
    state: int
    forbidden: int
    next_bit: str
    root: bool
    end: bool


@dataclass(frozen=True)
class Graph:
    colours: tuple[Colour, ...]
    edges: frozenset[tuple[int, str, int]]

    @property
    def end(self) -> int:
        ends = [i for i, c in enumerate(self.colours) if c.end]
        if len(ends) != 1:
            raise ValueError('Expected one distinguished endpoint')
        return ends[0]

    def target(self, source: int, label: str) -> int:
        out = [v for u, a, v in self.edges if u == source and a == label]
        if len(out) != 1:
            raise ValueError('Expected a unique edge: %r' % ((source, label),))
        return out[0]

    def outgoing(self) -> tuple[tuple[tuple[str, int], ...], ...]:
        out = [[] for _ in self.colours]
        for u, a, v in sorted(self.edges):
            out[u].append((a, v))
        return tuple(tuple(row) for row in out)


def column_mask(I: Instance, state: int) -> int:
    return sum(1 << p for p in range(len(I.delta)) if (p, state) in I.flags)


def graph_from_reference(I: Instance, B: Reference) -> Graph:
    """Direct prefix-function construction, including FULL-prefix fallback."""
    if not B.word or len(B.labels) != len(B.word) + 1:
        raise ValueError('A nonempty word and all cut labels are required')
    m = len(B.word)
    pi = prefix_function(B.word)
    colours = []
    edges = set()
    for j in range(m + 1):
        mask = 0
        for h in border_chain(pi, j):
            mask |= column_mask(I, B.labels[h])
        colours.append(Colour(B.labels[j], mask,
                              B.word[j] if j < m else '', j == 0, j == m))
        edges.add((j, 'F', pi[j]))
        if j < m:
            edges.add((j, 'S', j + 1))
        for a in '01':
            h = pi[j] if j == m else j
            while h and B.word[h] != a:
                h = pi[h]
            if B.word[h] == a:
                h += 1
            edges.add((j, 'K' + a, h))
    return Graph(tuple(colours), frozenset(edges))


def literal_graph(I: Instance, B: Reference) -> Graph:
    """Independent string-suffix construction; no prefix-function recurrence."""
    m = len(B.word)
    colours, edges = [], set()
    for j in range(m + 1):
        prefix = B.word[:j]
        borders = [h for h in range(j + 1) if prefix.endswith(B.word[:h])]
        mask = 0
        for h in borders:
            mask |= column_mask(I, B.labels[h])
        proper = [h for h in borders if h < j]
        fail = max(proper, default=0)
        edges.add((j, 'F', fail))
        if j < m:
            edges.add((j, 'S', j + 1))
        for a in '01':
            text = prefix + a
            dest = max(h for h in range(m + 1) if text.endswith(B.word[:h]))
            edges.add((j, 'K' + a, dest))
        colours.append(Colour(B.labels[j], mask,
                              B.word[j] if j < m else '', j == 0, j == m))
    return Graph(tuple(colours), frozenset(edges))


def first_return(B: str, C: str) -> bool:
    if not B or not C.startswith(B) or len(C) <= len(B):
        return False
    hit = C.find(B, 1)
    return hit >= 1 and hit + len(B) == len(C)


def local_extension(I: Instance, B: Reference, C: Reference,
                    require_safe: bool = True) -> tuple[Graph, tuple[int, ...]]:
    """Construct G_C using G_B and ONE base-graph walk only.

    No prefix-function computation on C is used. Origins for new vertices are
    the generator's successive KMP positions in G_B. Fresh endpoint fallback
    goes through the old endpoint, which can wrap to the first fresh vertex.
    """
    if not first_return(B.word, C.word) or C.labels[:len(B.labels)] != B.labels:
        raise ValueError('C must be a consistently labelled first return of B')
    if require_safe and not valid_reverse_prefix(I, B.word, B.labels):
        raise ValueError('Unsafe initial reference')
    G = graph_from_reference(I, B)
    m, n = len(B.word), len(C.word)
    ext = C.word[m:]
    first = m + 1
    h = G.target(m, 'F')
    origins = []
    prev = B.labels[-1]
    for offset, a in enumerate(ext, start=1):
        h = G.target(h, 'K' + a)
        p = C.labels[m + offset]
        if require_safe:
            if I.delta[p][int(a)] != prev or p in I.bad:
                raise ValueError('Undefined/unsafe reverse generator transition')
            if (p, p) in I.flags or G.colours[h].forbidden >> p & 1:
                raise ValueError('Generator introduced a forbidden border')
        if (h == m) != (offset == len(ext)):
            raise ValueError('Generator did not stop on its first full return')
        origins.append(h)
        prev = p
    colours = list(G.colours)
    c = colours[m]
    colours[m] = Colour(c.state, c.forbidden, ext[0], c.root, False)
    # The old endpoint's K edges are replaced; all other old edges survive.
    edges = {(u, a, v) for u, a, v in G.edges if not (u == m and a.startswith('K'))}
    edges.add((m, 'S', first))
    for a in '01':
        edges.add((m, 'K' + a, first if a == ext[0] else G.target(m, 'K' + a)))
    for offset, h in enumerate(origins, start=1):
        j = m + offset
        p = C.labels[j]
        end = j == n
        a_next = '' if end else C.word[j]
        colours.append(Colour(p, column_mask(I, p) | G.colours[h].forbidden,
                              a_next, False, end))
        edges.add((j, 'F', h))
        if end:
            for a in '01':
                edges.add((j, 'K' + a,
                           first if a == ext[0] else G.target(m, 'K' + a)))
        else:
            edges.add((j, 'S', j + 1))
            for a in '01':
                edges.add((j, 'K' + a,
                           j + 1 if a == a_next else G.target(h, 'K' + a)))
    return Graph(tuple(colours), frozenset(edges)), tuple(origins)


def allowed_actual(I: Instance, p: int, colour: Colour) -> bool:
    return p not in I.bad and (p, p) not in I.flags and not (colour.forbidden >> p & 1)


def finish_on_graph(I: Instance, G: Graph, allow_return: bool = False) -> Optional[tuple[str, tuple[int, ...]]]:
    """Existential DIRECTED regular-path query on G, with finite original control.

    Returns a labelled reverse extension, or None after exact finite exhaustion.
    Does not choose any new reference word.
    """
    end = G.end
    start = (G.colours[end].state, G.target(end, 'F'))
    todo = deque([start])
    parent = {start: None}
    while todo:
        q, h = todo.popleft()
        if q == I.start:
            word, labels, cur = [], [], (q, h)
            while parent[cur] is not None:
                old, a = parent[cur]
                word.append(a)
                labels.append(cur[0])
                cur = old
            return ''.join(reversed(word)), tuple(reversed(labels))
        for a in '01':
            t = G.target(h, 'K' + a)
            if t == end and not allow_return:
                continue
            for p, row in enumerate(I.delta):
                if row[int(a)] != q or not allowed_actual(I, p, G.colours[t]):
                    continue
                new = (p, t)
                if new not in parent:
                    parent[new] = ((q, h), a)
                    todo.append(new)
    return None


@dataclass(frozen=True)
class Automaton:
    """A finite path observer, with finite unary colour tests per control state.

    predicates contain tuples (field,value); all tests in a tuple are conjoined.
    Empty predicate means true. This executable sublanguage suffices for tests;
    the proof permits arbitrary finite Boolean colour predicates.
    """
    size: int
    start: int
    finals: frozenset[int]
    transitions: frozenset[tuple[int, str, int]]
    predicates: tuple[tuple[tuple[str, object], ...], ...]

    def permits(self, control: int, colour: Colour) -> bool:
        return all(getattr(colour, key) == value for key, value in self.predicates[control])


def query_path(G: Graph, A: Automaton, source: int, target: int,
               edges: Optional[frozenset[tuple[int, str, int]]] = None):
    """A shortest accepting product path; every (vertex,control) is unique."""
    if not A.permits(A.start, G.colours[source]):
        return None
    out = [[] for _ in G.colours]
    for u, a, v in sorted(G.edges if edges is None else edges):
        out[u].append((a, v))
    transitions = {}
    for q, a, p in sorted(A.transitions):
        transitions.setdefault((q, a), []).append(p)
    start = (source, A.start)
    todo = deque([start])
    parent = {start: None}
    while todo:
        node = todo.popleft()
        v, q = node
        if v == target and q in A.finals:
            result = []
            cur = node
            while parent[cur] is not None:
                prev, a = parent[cur]
                result.append((prev[0], prev[1], a, cur[0], cur[1]))
                cur = prev
            return tuple(reversed(result))
        for a, w in out[v]:
            for p in transitions.get((q, a), ()):
                if not A.permits(p, G.colours[w]):
                    continue
                nxt = (w, p)
                if nxt not in parent:
                    parent[nxt] = (node, a)
                    todo.append(nxt)
    return None


def classify_edge(m: int, n: int, edge: tuple[int, str, int]) -> str:
    u, a, v = edge
    if u <= m and v <= m:
        return 'core'
    if u <= m < v:
        if u != m or v != m + 1 or a not in ('S', 'K0', 'K1'):
            raise AssertionError('An unaccounted core-to-strip edge')
        return 'enter'
    if u > m >= v:
        return 'exit'
    if u == n and v == m + 1:
        return 'wrap'
    if v == u + 1 and a in ('S', 'K0', 'K1'):
        return 'forward'
    raise AssertionError('An unaccounted fresh-to-fresh edge')


def path_diagram(G: Graph, old_end: int, A: Automaton, source: int,
                 target: int, path):
    """Extract the bounded structural skeleton used by the proposed QE proof.

    The path may be arbitrarily long inside its core or forward pieces. The
    skeleton never discards equality between physically shared strip positions.
    """
    m, n = old_end, G.end
    if path is None:
        raise ValueError('An actual accepting path is required')
    configs = [(source, A.start)] + [(v, p) for u, q, a, v, p in path]
    if len(configs) != len(set(configs)):
        raise ValueError('Use a simple accepting product path')
    if configs[-1][0] != target or configs[-1][1] not in A.finals:
        raise ValueError('Wrong query endpoint')
    if not all(A.permits(q, G.colours[v]) for v, q in configs):
        raise ValueError('A colour test failed')
    entries = sum(v == m + 1 for v, q in configs)
    assert entries <= A.size
    marked = {m + 1, n}
    if source > m:
        marked.add(source)
    if target > m:
        marked.add(target)
    pieces = []
    for u, q, a, v, p in path:
        if (u, a, v) not in G.edges or (q, a, p) not in A.transitions:
            raise ValueError('Invalid path edge')
        kind = classify_edge(m, n, (u, a, v))
        if kind in ('enter', 'exit', 'wrap'):
            if u > m: marked.add(u)
            if v > m: marked.add(v)
        # Maximal homogeneous core/forward pieces, portal edges kept separately.
        if pieces and kind in ('core', 'forward') and pieces[-1]['kind'] == kind:
            pieces[-1]['end'] = (v, p)
            pieces[-1]['edges'].append((u, q, a, v, p))
        else:
            pieces.append({'kind': kind, 'start': (u, q), 'end': (v, p),
                           'edges': [(u, q, a, v, p)]})
    fresh_runs = sum(piece['kind'] in ('enter', 'wrap') for piece in pieces)
    fresh_runs += int(source > m)
    assert fresh_runs <= A.size + 1
    # Start/end of every forward span and every fresh query variable are marked.
    for piece in pieces:
        if piece['kind'] == 'forward':
            marked.add(piece['start'][0]); marked.add(piece['end'][0])
    assert len(marked) <= 2 * (A.size + 1) + 4
    return {'pieces': pieces, 'marked_positions': sorted(marked),
            'fresh_runs': fresh_runs, 'entry_product_configurations': entries,
            'bound': A.size + 1}


def forward_observer(G: Graph, A: Automaton, left: int, right: int,
                     initial: Optional[frozenset[int]] = None) -> frozenset[int]:
    """Stream a physically shared forward interval without separate word choices."""
    if left > right:
        return frozenset()
    states = frozenset({A.start}) if initial is None else initial
    states = frozenset(q for q in states if A.permits(q, G.colours[left]))
    for j in range(left, right):
        labels = {a for u, a, v in G.edges if u == j and v == j + 1}
        states = frozenset(p for q, a, p in A.transitions
                           if q in states and a in labels and A.permits(p, G.colours[j + 1]))
    return states


def exact_edge_word(word: tuple[str, ...]) -> Automaton:
    return Automaton(len(word) + 1, 0, frozenset({len(word)}),
                     frozenset((i, a, i + 1) for i, a in enumerate(word)),
                     tuple(() for _ in range(len(word) + 1)))

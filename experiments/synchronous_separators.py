"""Exact encoding-aware preprocessing for terminal BorderAvoid instances.

A Boolean colour is assigned to original transitions. Along every synchronized
pair path rooted at a flag, aligned transitions must have the same colour.
Transitions on productive cycles are forced data (0); transitions entering a
terminal final are forced separators (1). If these finite constraints are
consistent, the original instance is encoded word-for-word into the existing
10/11-data, 00-separator format. C053 then decides the encoded instance exactly.

Failure of the colouring constraints or any downstream resource cap is UNKNOWN,
never NO. See notes/2026-09-08-synchronous-separators.md.
"""
from collections import deque
from dataclasses import dataclass
from typing import FrozenSet, Optional, Tuple

from border_lab import Instance, witness, border_witness
from marker_certificate import marker_decision, marker_structure
from terminal_realization import validate


Transition = Tuple[int, int]


@dataclass(frozen=True)
class SeparatorCertificate:
    marked: FrozenSet[Transition]
    equality_classes: int
    pair_vertices: int
    cycle_edges: int
    final_edges: int


class _UF:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x != y:
            self.p[y] = x


def _reach(delta, start):
    seen = {start}
    todo = [start]
    for p in todo:
        for q in delta[p]:
            if q >= 0 and q not in seen:
                seen.add(q)
                todo.append(q)
    return seen


def separator_certificate(I: Instance):
    """Return a finite synchronous-separator colouring, or NOT_APPLICABLE.

    The test is deliberately conservative: all graph cycles, including
    unproductive ones, are forced unmarked. This can reject useful colourings
    but cannot create a false decision.
    """
    validate(I)
    if I.alphabet != '01' or any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        return {'status': 'NOT_APPLICABLE',
                'reason': 'Binary terminal accepting states are required'}, None
    edges = [(p, a) for p, row in enumerate(I.delta)
             for a, q in enumerate(row) if q >= 0]
    index = {edge: i for i, edge in enumerate(edges)}
    uf = _UF(len(edges))

    # Equality constraints: if an original flagged comparison can keep reading
    # the same letters, its two aligned transitions must receive equal colours.
    pair_seen = set(I.flags)
    todo = deque(pair_seen)
    while todo:
        p, q = todo.popleft()
        for a in range(2):
            r, s = I.delta[p][a], I.delta[q][a]
            if r < 0 or s < 0:
                continue
            uf.union(index[p, a], index[q, a])
            if (r, s) not in pair_seen:
                pair_seen.add((r, s))
                todo.append((r, s))

    reaches = [_reach(I.delta, p) for p in range(len(I.delta))]
    requirements = []
    cycle_edges = final_edges = 0
    for edge in edges:
        p, a = edge
        q = I.delta[p][a]
        if p in reaches[q]:
            requirements.append((edge, 0, 'cycle'))
            cycle_edges += 1
        if q in I.final:
            requirements.append((edge, 1, 'final'))
            final_edges += 1

    values = {}
    for edge, value, source in requirements:
        root = uf.find(index[edge])
        previous = values.get(root)
        if previous is not None and previous != value:
            return {'status': 'NOT_APPLICABLE',
                    'reason': 'Synchrony equates a required separator with a cycle edge',
                    'conflict_edge': edge, 'conflict_source': source,
                    'pair_vertices': len(pair_seen)}, None
        values[root] = value

    marked = frozenset(edge for edge in edges
                       if values.get(uf.find(index[edge]), 0) == 1)
    cert = SeparatorCertificate(marked, len({uf.find(i) for i in range(len(edges))}),
                                len(pair_seen), cycle_edges, final_edges)
    return {'status': 'CERTIFIED', 'marked': sorted(marked),
            'equality_classes': cert.equality_classes,
            'pair_vertices': cert.pair_vertices,
            'cycle_edges': cycle_edges, 'final_edges': final_edges}, cert


def compile_separators(I: Instance, certificate: SeparatorCertificate) -> Instance:
    """Encode one original transition as 1a, followed by 00 iff marked.

    Original states are exactly code boundaries and retain all annotations.
    Helpers carry no flags, Bad labels, or finality.
    """
    validate(I)
    marked = certificate.marked
    k = len(I.delta)
    table = [[-1, -1] for _ in range(k)]

    def node():
        q = len(table)
        table.append([-1, -1])
        return q

    for p, row in enumerate(I.delta):
        defined = [a for a, q in enumerate(row) if q >= 0]
        if not defined:
            continue
        data = node()
        table[p][1] = data
        for a in defined:
            q = row[a]
            if (p, a) not in marked:
                table[data][a] = q
            else:
                first = node()
                second = node()
                table[data][a] = first
                table[first][0] = second
                table[second][0] = q
    return Instance(tuple(tuple(row) for row in table), I.final, I.flags,
                    I.bad, I.start, '01')


def encode_word(I: Instance, word: str, certificate: SeparatorCertificate) -> str:
    run = I.run(word)
    if run is None:
        raise ValueError('Word must have a defined original run')
    out = []
    for i, a in enumerate(word):
        out.append('1' + a)
        if (run[i], int(a)) in certificate.marked:
            out.append('00')
    return ''.join(out)


def separator_decision(I: Instance, max_schemas: Optional[int] = 5000,
                       max_states: Optional[int] = 200000,
                       max_transitions: Optional[int] = 2000000):
    """Exact decision whenever the synchronous-separator certificate exists.

    The returned witness is decoded back to the original alphabet and checked
    by both independent original predicates. Certificate failure stays UNKNOWN.
    """
    summary, cert = separator_certificate(I)
    if cert is None:
        return dict(status='UNKNOWN', certificate=summary)
    J = compile_separators(I, cert)
    # The theorem predicts that C053's paired certificate must apply. Keep this
    # executable assertion close to the integration boundary.
    structures = []
    for f in sorted(J.final):
        structure, _, _ = marker_structure(J, f, code='paired')
        structures.append(structure)
        if structure['status'] not in ('CERTIFIED', 'EMPTY_SLICE', 'EMPTY_WORD'):
            raise AssertionError(('Synchronous separator compilation escaped C053', structure))
    answer = marker_decision(J, max_schemas=max_schemas, max_states=max_states,
                             max_transitions=max_transitions)
    if answer['status'] != 'YES':
        return dict(answer, certificate=summary, compiled_states=len(J.delta),
                    compiled_structures=structures)

    encoded = answer['word']
    # Decode the unique token stream: 1a is one original letter; optional 00
    # immediately following it records only the transition colour.
    original = []
    i = 0
    while i < len(encoded):
        if i + 1 >= len(encoded) or encoded[i] != '1':
            raise AssertionError('Invalid compiled witness token stream')
        original.append(encoded[i+1])
        i += 2
        if i + 1 < len(encoded) and encoded[i:i+2] == '00':
            i += 2
    word = ''.join(original)
    assert encode_word(I, word, cert) == encoded
    assert witness(I, word) and border_witness(I, word)
    return dict(answer, word=word, encoded_word=encoded, certificate=summary,
                compiled_states=len(J.delta), compiled_structures=structures)

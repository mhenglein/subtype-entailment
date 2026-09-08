"""Exact encoding-aware preprocessing for terminal BorderAvoid instances.

Boolean transition colours are synchronized along every pair path rooted at a
flag. A compiled transition is 1a, followed by 00 exactly when marked. This
preserves all flagged suffix comparisons. Two finite certificates are exposed:
(1) force every cycle edge to data and use C053; (2) force only final edges to
separators and use C056, which permits marker cycles before relevant targets.
Failure or resource exhaustion is UNKNOWN, never NO.
"""
from collections import deque
from dataclasses import dataclass
from typing import FrozenSet, Optional, Tuple

from border_lab import Instance, witness, border_witness
from marker_certificate import marker_decision, marker_structure
from target_frontier import Limits as FrontierLimits, target_frontier_decision
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
    def __init__(self, n): self.p = list(range(n))
    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]; x = self.p[x]
        return x
    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x != y: self.p[y] = x


def _reach(delta, start):
    seen, todo = {start}, [start]
    for p in todo:
        for q in delta[p]:
            if q >= 0 and q not in seen:
                seen.add(q); todo.append(q)
    return seen


def _colouring(I, force_cycles):
    validate(I)
    if I.alphabet != '01' or any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        return {'status':'NOT_APPLICABLE','reason':'Binary terminal accepting states are required'}, None
    edges = [(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row) if q >= 0]
    index = {e:i for i,e in enumerate(edges)}
    uf = _UF(len(edges))
    pair_seen, todo = set(I.flags), deque(I.flags)
    while todo:
        p,q = todo.popleft()
        for a in range(2):
            r,s = I.delta[p][a], I.delta[q][a]
            if r < 0 or s < 0: continue
            uf.union(index[p,a], index[q,a])
            if (r,s) not in pair_seen:
                pair_seen.add((r,s)); todo.append((r,s))
    reaches = [_reach(I.delta,p) for p in range(len(I.delta))]
    requirements=[]; cycle_edges=final_edges=0
    for edge in edges:
        p,a=edge; q=I.delta[p][a]
        if p in reaches[q]:
            cycle_edges += 1
            if force_cycles: requirements.append((edge,0,'cycle'))
        if q in I.final:
            requirements.append((edge,1,'final')); final_edges += 1
    values={}
    for edge,value,source in requirements:
        root=uf.find(index[edge]); previous=values.get(root)
        if previous is not None and previous != value:
            return {'status':'NOT_APPLICABLE',
                    'reason':'Synchrony equates a required separator with a forced data edge',
                    'conflict_edge':edge,'conflict_source':source,
                    'pair_vertices':len(pair_seen)}, None
        values[root]=value
    marked=frozenset(e for e in edges if values.get(uf.find(index[e]),0)==1)
    cert=SeparatorCertificate(marked,len({uf.find(i) for i in range(len(edges))}),
                              len(pair_seen),cycle_edges,final_edges)
    return {'status':'CERTIFIED','marked':sorted(marked),
            'equality_classes':cert.equality_classes,'pair_vertices':cert.pair_vertices,
            'cycle_edges':cycle_edges,'final_edges':final_edges,
            'cycle_edges_forced_data':bool(force_cycles)}, cert


def separator_certificate(I):
    """C053 certificate: synchronized finals marked, every cycle edge data."""
    return _colouring(I, True)


def frontier_separator_certificate(I):
    """C056 certificate candidate: synchronized finals marked; early cycles allowed."""
    return _colouring(I, False)


def compile_separators(I, certificate):
    """Encode one original transition as 1a, followed by 00 iff marked."""
    validate(I); marked=certificate.marked; k=len(I.delta)
    table=[[-1,-1] for _ in range(k)]
    def node(): table.append([-1,-1]); return len(table)-1
    for p,row in enumerate(I.delta):
        defined=[a for a,q in enumerate(row) if q>=0]
        if not defined: continue
        data=node(); table[p][1]=data
        for a in defined:
            q=row[a]
            if (p,a) not in marked: table[data][a]=q
            else:
                first,second=node(),node(); table[data][a]=first
                table[first][0]=second; table[second][0]=q
    return Instance(tuple(tuple(row) for row in table),I.final,I.flags,I.bad,I.start,'01')


def encode_word(I,word,certificate):
    run=I.run(word)
    if run is None: raise ValueError('Word must have a defined original run')
    out=[]
    for i,a in enumerate(word):
        out.append('1'+a)
        if (run[i],int(a)) in certificate.marked: out.append('00')
    return ''.join(out)


def _decode_positive(I, cert, answer, summary, compiled_states, extra):
    if answer['status'] != 'YES': return dict(answer,certificate=summary,compiled_states=compiled_states,**extra)
    encoded=answer['word']; original=[]; i=0
    while i < len(encoded):
        if i+1 >= len(encoded) or encoded[i] != '1': raise AssertionError('Invalid compiled token stream')
        original.append(encoded[i+1]); i += 2
        if i+1 < len(encoded) and encoded[i:i+2]=='00': i += 2
    word=''.join(original)
    assert encode_word(I,word,cert)==encoded
    assert witness(I,word) and border_witness(I,word)
    return dict(answer,word=word,encoded_word=encoded,certificate=summary,
                compiled_states=compiled_states,**extra)


def separator_decision(I,max_schemas=5000,max_states=200000,max_transitions=2000000):
    """Exact on the acyclic-separator C053 certificate."""
    summary,cert=separator_certificate(I)
    if cert is None: return dict(status='UNKNOWN',certificate=summary)
    J=compile_separators(I,cert); structures=[]
    for f in sorted(J.final):
        structure,_,_=marker_structure(J,f,code='paired'); structures.append(structure)
        if structure['status'] not in ('CERTIFIED','EMPTY_SLICE','EMPTY_WORD'):
            raise AssertionError(('Synchronous compilation escaped C053',structure))
    answer=marker_decision(J,max_schemas=max_schemas,max_states=max_states,
                           max_transitions=max_transitions)
    return _decode_positive(I,cert,answer,summary,len(J.delta),{'compiled_structures':structures})


def frontier_separator_decision(I,limits=FrontierLimits()):
    """Exact when the minimal synchronous colouring satisfies C056.

    Marker cycles forced by synchronization with a terminal edge are allowed
    before the first relevant target. A target-reachable marker cycle or cap
    remains UNKNOWN in the downstream solver.
    """
    summary,cert=frontier_separator_certificate(I)
    if cert is None: return dict(status='UNKNOWN',certificate=summary)
    J=compile_separators(I,cert)
    answer=target_frontier_decision(J,limits)
    return _decode_positive(I,cert,answer,summary,len(J.delta),{'downstream':'C056'})

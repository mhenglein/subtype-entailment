"""G-specific last-aligned separator compiler and finite-spectrum wrapper.

Unlike synchronous_separators.py, equality constraints are imposed only on
productive synchronized pair paths that can witness a *last-aligned* forbidden
comparison.  Flags may root such a path but a positive-step destination that is
itself flagged is excluded.  Every transition entering the sole terminal final
is marked; the least synchronized marking is then compiled to paired tokens.

On a boundary-normalized single-final terminal slice this preserves witnesshood:
every bad word has a minimum-target-suffix violation, hence a last-aligned one;
that comparison follows the retained pair graph and survives decoration.  A
compiled bad comparison decodes to an original bad comparison.

The semantic wrapper composes this compiler with macro_marker_spectrum and
macro_marker_tail.  Unbounded spectra or caps are UNKNOWN, never NO.
"""
from collections import deque
from dataclasses import dataclass
from typing import FrozenSet, Tuple

from border_lab import Instance, witness, border_witness
from macro_marker_spectrum import semantic_macro_decision
from synchronous_separators import SeparatorCertificate, compile_separators
from target_frontier import Limits
from terminal_realization import validate

Transition = Tuple[int, int]
Pair = Tuple[int, int]


class _UF:
    def __init__(self,n): self.p=list(range(n))
    def find(self,x):
        while self.p[x]!=x:
            self.p[x]=self.p[self.p[x]]; x=self.p[x]
        return x
    def union(self,x,y):
        x,y=self.find(x),self.find(y)
        if x!=y: self.p[y]=x


def _boundary_normalized(I):
    if len(I.final)!=1 or I.bad:
        return False
    f=next(iter(I.final))
    if any(any(q>=0 for q in I.delta[f]) for _ in (0,)):
        return False
    return not any(p==q or q==f for p,q in I.flags)


def last_aligned_certificate(I):
    """Return the least marking preserving every last-aligned comparison.

    Scope is deliberately explicit: one terminal final, no Bad states, no
    diagonal flags and no flag targeting the final (i.e. an already normalized
    slice).  Failure of this scope check is NOT_APPLICABLE.
    """
    validate(I)
    if I.alphabet!='01' or not _boundary_normalized(I):
        return {'status':'NOT_APPLICABLE',
                'reason':'Boundary-normalized binary single-final terminal slice required'},None
    f=next(iter(I.final)); k=len(I.delta)
    edges=[(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row) if q>=0]
    edge_ix={e:i for i,e in enumerate(edges)}

    roots={pair for pair in I.flags if pair[0]!=pair[1] and pair[1]!=f}
    # Pair vertices exclude right-final endpoints; endpoints are represented
    # separately and have no outgoing synchronized continuation.
    vertices={(p,q) for p in range(k) for q in range(k)
              if p!=q and p!=f and q!=f}
    pair_edges={v:[] for v in vertices}
    endpoints=set()
    for p,q in vertices:
        for a in range(2):
            r,s=I.delta[p][a],I.delta[q][a]
            if r<0 or s<0 or r==f or r==s:
                continue
            dest=(r,s)
            if s==f:
                endpoints.add(dest)
                pair_edges[p,q].append((a,dest,True))
            elif dest not in I.flags and dest in vertices:
                pair_edges[p,q].append((a,dest,False))

    # Root reachability.
    reachable=set(v for v in roots if v in vertices)
    todo=deque(reachable)
    while todo:
        v=todo.popleft()
        for _,dest,is_end in pair_edges[v]:
            if not is_end and dest not in reachable:
                reachable.add(dest); todo.append(dest)

    # Reverse co-reachability from an endpoint (r,f).
    back={v:[] for v in vertices}
    coreach=set()
    for v,xs in pair_edges.items():
        for _,dest,is_end in xs:
            if is_end:
                coreach.add(v)
            else:
                back[dest].append(v)
    todo=deque(coreach)
    while todo:
        v=todo.popleft()
        for u in back[v]:
            if u not in coreach:
                coreach.add(u); todo.append(u)
    live=reachable & coreach

    uf=_UF(len(edges))
    retained=0
    for p,q in live:
        for a,dest,is_end in pair_edges[p,q]:
            if is_end or dest in live:
                uf.union(edge_ix[p,a],edge_ix[q,a]); retained+=1

    forced=set()
    for p,a in edges:
        if I.delta[p][a]==f:
            forced.add(uf.find(edge_ix[p,a]))
    marked=frozenset(e for e in edges if uf.find(edge_ix[e]) in forced)
    cert=SeparatorCertificate(marked,
        len({uf.find(i) for i in range(len(edges))}),len(live),0,
        sum(1 for p,a in edges if I.delta[p][a]==f))
    summary={'status':'CERTIFIED','marked':sorted(marked),
             'roots':len(roots),'live_pair_vertices':len(live),
             'retained_pair_edges':retained,
             'equality_classes':cert.equality_classes,
             'final_edges':cert.final_edges,
             'constraint':'productive last-aligned pair paths only'}
    return summary,cert


def compile_last_aligned(I):
    summary,cert=last_aligned_certificate(I)
    if cert is None: return summary,None
    return summary,compile_separators(I,cert)


def last_aligned_decision(I,limits=Limits()):
    """Exact when the compiled last-aligned separator spectrum is finite."""
    summary,J=compile_last_aligned(I)
    if J is None: return dict(status='UNKNOWN',certificate=summary)
    out=semantic_macro_decision(J,limits)
    if out['status']=='YES':
        # Decode paired transition tokens: every original letter is 1a and an
        # optional following 00 is decoration only.
        encoded=out['word']; letters=[]; i=0
        while i<len(encoded):
            if i+1>=len(encoded) or encoded[i]!='1':
                raise AssertionError('Invalid paired compiled witness')
            letters.append(encoded[i+1]); i+=2
            if i+1<len(encoded) and encoded[i:i+2]=='00': i+=2
        word=''.join(letters)
        assert witness(I,word) and border_witness(I,word)
        return dict(out,word=word,encoded_word=encoded,certificate=summary)
    return dict(out,certificate=summary)

"""Finite symbolic promotion-preimage compiler; research implementation.

All input observers and predicates have finite explicit/structural syntax.
The compiler has no concrete base-graph or reference-word argument. This is
not a proof assistant: the accompanying closure proof needs external review.
Resource exhaustion is UNKNOWN, never a negative mathematical verdict.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import product
from math import prod
from typing import Any, Iterator
from rank_query_graphs import Colour, Graph, column_mask

LABELS = ('F', 'S', 'K0', 'K1')


class Exhausted(RuntimeError):
    pass


@dataclass
class Budget:
    maximum: int | None = None
    used: int = 0

    def tick(self, amount=1):
        self.used += amount
        if self.maximum is not None and self.used > self.maximum:
            raise Exhausted('Explicit work cap')


@dataclass(frozen=True)
class Map:
    kind: str = 'identity'
    args: tuple = ()

    def apply(self, c: Colour) -> Colour:
        if self.kind == 'identity': return c
        if self.kind == 'constant': return self.args[0]
        if self.kind == 'core':
            return Colour(c.state, c.forbidden, self.args[0], c.root, False) if c.end else c
        if self.kind == 'fresh':
            q, mask, nxt = self.args
            return Colour(q, mask | c.forbidden, nxt, False, nxt == '')
        raise ValueError('Unknown finite colour map: ' + self.kind)


@dataclass(frozen=True)
class Test:
    kind: str = 'true'
    args: tuple = ()

    def holds(self, c: Colour) -> bool:
        k, a = self.kind, self.args
        if k == 'true': return True
        if k == 'false': return False
        if k == 'field': return getattr(c, a[0]) == a[1]
        if k == 'colour': return c == a[0]
        if k == 'clear': return not (getattr(c, a[0]) >> a[1] & 1)
        if k == 'and': return all(t.holds(c) for t in a)
        if k == 'not': return not a[0].holds(c)
        if k == 'mapped': return a[1].holds(a[0].apply(c))
        if k == 'allows': return a[0].allows(a[1], a[2].apply(c))
        if k == 'portal':
            obs, q, p, label, left, right = a
            x, y = left.apply(c), right.apply(c)
            return obs.allows(q, x) and obs.allows(p, y) and p in obs.move(q, label, x, y)
        raise ValueError('Unknown finite colour predicate: ' + k)


TRUE = Test()
FALSE = Test('false')

def conj(*ts):
    ts = tuple(t for t in ts if t != TRUE)
    if FALSE in ts: return FALSE
    return TRUE if not ts else ts[0] if len(ts) == 1 else Test('and', ts)


def fld(name, value): return Test('field', (name, value))


def fresh(I, q, nxt): return Map('fresh', (q, column_mask(I, q), nxt))


def radix_encode(values, sizes):
    n = 0
    for x, s in zip(values, sizes):
        if not 0 <= x < s: raise ValueError('Control out of range')
        n = n*s+x
    return n


def radix_decode(value, sizes):
    out=[]
    for s in reversed(sizes):
        out.append(value%s); value//=s
    if value: raise ValueError('Control out of range')
    return tuple(reversed(out))


@dataclass(frozen=True)
class Observer:
    kind: str
    size: int
    initial: tuple[int, ...]
    final: frozenset[int]
    data: tuple

    def __post_init__(self):
        if self.size < 1 or any(q < 0 or q >= self.size for q in (*self.initial, *self.final)):
            raise ValueError('Malformed observer controls')

    def allows(self, q, c):
        k,a = self.kind,self.data
        if not 0 <= q < self.size: return False
        if k == 'table': return a[0][q].holds(c)
        if k == 'slice': return a[0].allows(q,c)
        if k == 'core': return a[0].allows(q,Map('core',(a[1],)).apply(c))
        if k == 'edge': return a[1+q].holds(c)
        if k == 'interval':
            I, active, sizes = a
            state = radix_decode(q,sizes); real,nxt,seen = state[:3]; controls=state[3:]
            if real in I.bad or (real,real) in I.flags or c.forbidden >> real & 1: return False
            if (nxt == 2) != c.end: return False
            fc = fresh(I,real,('0','1','')[nxt]).apply(c)
            return all(o.allows(t,fc) for o,t in zip(active,controls))
        if k == 'finish': return not c.end
        raise ValueError('Unknown observer kind '+k)

    def move(self, q, label, c, d):
        k,a = self.kind,self.data
        if k == 'table': return tuple(t for s,e,t in a[1] if s==q and e==label)
        if k == 'slice': return a[0].move(q,label,c,d)
        if k == 'core':
            o,b = a
            if c.end and label == 'K'+b: return ()
            f=Map('core',(b,)); return o.move(q,label,f.apply(c),f.apply(d))
        if k == 'edge':
            edge,_,_,semantic = a
            if q != 0 or label != edge: return ()
            if semantic is None: return (1,)
            o,s,t,physical,left,right = semantic
            return (1,) if t in o.move(s,physical,left.apply(c),right.apply(d)) else ()
        if k == 'interval':
            I, active, sizes = a
            state=radix_decode(q,sizes); real,nxt,seen=state[:3]; controls=state[3:]
            if nxt==2 or label!='K'+str(nxt) or c.end: return ()
            fc=fresh(I,real,str(nxt)).apply(c)
            out=set()
            for p,row in enumerate(I.delta):
                if row[nxt]!=real or p in I.bad or (p,p) in I.flags or d.forbidden>>p&1: continue
                for nb in ((2,) if d.end else (0,1)):
                    gc=fresh(I,p,('0','1','')[nb]).apply(d)
                    choices=[]
                    for o,t in zip(active,controls):
                        good=set(o.move(t,'S',fc,gc)) | set(o.move(t,'K'+str(nxt),fc,gc))
                        choices.append(tuple(sorted(x for x in good if o.allows(x,gc))))
                    for new in product(*choices):
                        out.add(radix_encode((p,nb,1,*new),sizes))
            return tuple(sorted(out))
        if k == 'finish':
            I=a[0]
            if label not in ('K0','K1') or d.end: return ()
            return tuple(p for p,row in enumerate(I.delta) if row[int(label[-1])]==q
                         and p not in I.bad and (p,p) not in I.flags and not d.forbidden>>p&1)
        raise ValueError('Unknown observer kind '+k)


def table(size, edges=(), initial=(0,), final=None, predicates=None):
    return Observer('table',size,tuple(initial),frozenset(range(size) if final is None else final),
                    (tuple(predicates or (TRUE,)*size),tuple(sorted(set(edges)))))


def slice_observer(o,q,p):
    return Observer('slice',o.size,(q,),frozenset({p}),(o,))


def core_observer(o,first):
    return Observer('core',o.size,o.initial,o.final,(o,first))


def one_edge(label,left=TRUE,right=TRUE,semantic=None):
    return Observer('edge',2,(0,),frozenset({1}),(label,left,right,semantic))


def interval_observer(I,active,left,right):
    # left/right: actual reverse state, next bit (0,1,''), observer controls.
    sizes=(len(I.delta),3,2,*(o.size for o in active))
    def at(boundary,seen):
        q,bit,controls=boundary
        return radix_encode((q,('0','1','').index(bit),seen,*controls),sizes)
    return Observer('interval',prod(sizes),(at(left,0),),frozenset({at(right,1)}),
                    (I,tuple(active),sizes))


@dataclass(frozen=True)
class Atom:
    observer: Observer
    source: str
    target: str


@dataclass(frozen=True)
class Query:
    variables: tuple[str,...]
    tests: tuple[tuple[str,Test],...]=()
    equal: tuple[tuple[str,str],...]=()
    unequal: tuple[tuple[str,str],...]=()
    atoms: tuple[Atom,...]=()

    def __post_init__(self):
        if len(set(self.variables))!=len(self.variables): raise ValueError('Duplicate variable')
        used={v for v,_ in self.tests}|{v for a in (*self.equal,*self.unequal) for v in a}
        used|={v for a in self.atoms for v in (a.source,a.target)}
        if not used<=set(self.variables): raise ValueError('Undeclared vertex')

    @property
    def weight(self):
        return 1+len(self.variables)+len(self.atoms)+sum(a.observer.size for a in self.atoms)


@dataclass(frozen=True)
class Model:
    assignment: dict[str,int]
    paths: tuple[tuple,...]


def path(G,o,source,target,budget=None):
    budget=budget or Budget()
    out=G.outgoing(); todo=deque(); parent={}
    for q in o.initial:
        if o.allows(q,G.colours[source]):
            node=(source,q);todo.append(node);parent[node]=None
    while todo:
        budget.tick();v,q=todo.popleft()
        if v==target and q in o.final:
            steps=[];cur=(v,q)
            while parent[cur] is not None:
                old,e=parent[cur];steps.append((old[0],old[1],e,cur[0],cur[1]));cur=old
            return (cur[1],tuple(reversed(steps)))
        for e,w in out[v]:
            for p in o.move(q,e,G.colours[v],G.colours[w]):
                node=(w,p)
                if o.allows(p,G.colours[w]) and node not in parent:
                    parent[node]=((v,q),e);todo.append(node)
    return None


def model(G,Q,budget=None):
    """Complete finite CSP evaluation, with AC-style domain propagation."""
    budget=budget or Budget();n=len(G.colours)
    domains={v:set(range(n)) for v in Q.variables}
    for v,t in Q.tests: domains[v]&={i for i,c in enumerate(G.colours) if t.holds(c)}
    relations=[];witnesses=[]
    for x,y in Q.equal: relations.append((x,y,{(i,i) for i in range(n)}))
    for x,y in Q.unequal: relations.append((x,y,{(i,j) for i in range(n) for j in range(n) if i!=j}))
    for atom in Q.atoms:
        R={};
        for i in domains[atom.source]:
            for j in domains[atom.target]:
                v=path(G,atom.observer,i,j,budget)
                if v is not None:R[i,j]=v
        witnesses.append(R);relations.append((atom.source,atom.target,set(R)))
    def search(D):
        budget.tick();D={v:set(d) for v,d in D.items()}
        changed=True
        while changed:
            changed=False
            for x,y,R in relations:
                rx={i for i,j in R if i in D[x] and j in D[y] and (x!=y or i==j)}
                ry={j for i,j in R if i in D[x] and j in D[y] and (x!=y or i==j)}
                if rx!=D[x]:D[x]=rx;changed=True
                if ry!=D[y]:D[y]=ry;changed=True
            if any(not d for d in D.values()):return None
        if all(len(d)==1 for d in D.values()):return {v:next(iter(d)) for v,d in D.items()}
        v=min((v for v in D if len(D[v])>1),key=lambda v:len(D[v]))
        for i in sorted(D[v]):
            E=dict(D);E[v]={i};ans=search(E)
            if ans is not None:return ans
        return None
    assignment=search(domains)
    if assignment is None:return None
    ps=tuple(R[assignment[a.source],assignment[a.target]] for a,R in zip(Q.atoms,witnesses))
    return Model(assignment,ps)

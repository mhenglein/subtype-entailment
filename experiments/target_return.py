#!/usr/bin/env python3
"""Source-sensitive target-return elimination for terminal BorderAvoid.

Complete on the proved return-closed class, not on arbitrary instances.
A failed certificate or resource cap is UNKNOWN. State labels retain ORIGINAL
states through every regular restriction; deleting a target deletes its entire
original column, not a single expanded monitor state. Standard library only.
"""
from __future__ import annotations
from collections import Counter, deque
from dataclasses import dataclass, asdict
from pathlib import Path
import argparse
import hashlib
import json
from typing import Optional
from target_anchor import Instance, normalize, witness, reverse_witness

BASE = 'b79bc02d5a669fde60484a463941b16e03805050'
Word = tuple[int, ...]


class Capped(Exception):
    """An incomplete finite computation, never evidence of nonexistence."""


@dataclass(frozen=True)
class Limits:
    states: Optional[int] = 10000
    pair_states: Optional[int] = 200000
    patterns: Optional[int] = 10000
    nodes: Optional[int] = 10000
    def __post_init__(self):
        for value in asdict(self).values():
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError('Caps must be positive integers or None')


@dataclass(frozen=True)
class Domain:
    delta: tuple[tuple[int, ...], ...]
    start: int
    final: int
    labels: tuple[int, ...]
    def __post_init__(self):
        k = len(self.delta)
        if not k or not (0 <= self.start < k and 0 <= self.final < k):
            raise ValueError('Invalid domain start/final')
        a = len(self.delta[0])
        if any(type(t) is not int or t < 0 for t in self.labels):
            raise ValueError('Original-state labels must be nonnegative integers')
        if not a or len(self.labels) != k or any(len(r) != a for r in self.delta):
            raise ValueError('Invalid domain dimensions')
        if any(type(q) is not int or not -1 <= q < k for r in self.delta for q in r):
            raise ValueError('Invalid domain transition')
        if any(q != -1 for q in self.delta[self.final]):
            raise ValueError('The accepting state must be terminal')
    @property
    def k(self): return len(self.delta)
    @property
    def alphabet(self): return len(self.delta[0])
    def run(self, word: Word, start=None):
        q = self.start if start is None else start
        if not 0 <= q < self.k: raise ValueError('Invalid run start')
        trace = [q]
        for a in word:
            if type(a) is not int or not 0 <= a < self.alphabet:
                raise ValueError('Invalid alphabet symbol')
            q = self.delta[q][a]
            if q < 0: return None
            trace.append(q)
        return tuple(trace)
    def accepts(self, w):
        c = self.run(tuple(w))
        return c is not None and c[-1] == self.final
    def json(self):
        return dict(delta=self.delta, start=self.start, final=self.final, labels=self.labels)
    def digest(self):
        return hashlib.sha256(json.dumps(self.json(), sort_keys=True).encode()).hexdigest()


def reachable(adj, starts):
    found = set(starts)
    todo = list(sorted(found))
    for p in todo:
        for q in adj[p]:
            if q not in found: found.add(q); todo.append(q)
    return found


def trim(A: Domain):
    adj = [tuple(q for q in row if q >= 0) for row in A.delta]
    rev = [[] for _ in adj]
    for p, row in enumerate(adj):
        for q in row: rev[q].append(p)
    live = reachable(adj, [A.start]) & reachable(rev, [A.final])
    if A.start not in live: return None
    order = sorted(live); ids = {p:i for i,p in enumerate(order)}
    return Domain(tuple(tuple(ids.get(q,-1) for q in A.delta[p]) for p in order),
                  ids[A.start], ids[A.final], tuple(A.labels[p] for p in order))


def shortest(A: Domain, start: int, goal, allow=lambda q: True):
    if not allow(start): return None
    queue = deque([start]); parent = {start:None}
    while queue:
        p = queue.popleft()
        if goal(p):
            w=[]
            while parent[p] is not None: p,a=parent[p]; w.append(a)
            return tuple(reversed(w))
        for a,q in enumerate(A.delta[p]):
            if q >= 0 and allow(q) and q not in parent:
                parent[q]=(p,a); queue.append(q)
    return None


def return_certificate(A: Domain, flags, target: int, limits=Limits()):
    """Productive synchronized returns preserve an incoming target column.

    A return means equality of ORIGINAL TARGET LABELS, not equality of monitor
    states. Merge exclusion also uses original labels. Pair paths are a sound
    overapproximation of comparisons on one accepted word. Failed certificates
    report a pair-path obstruction, not a false witness or mathematical NO.
    """
    sizes=Counter(A.labels)
    pair_count=sum(A.k-sizes[A.labels[p]] for p in range(A.k) if p != A.final)
    if limits.pair_states is not None and pair_count>limits.pair_states:
        raise Capped('synchronized-pair state cap')
    vertices=[(p,q) for p in range(A.k) for q in range(A.k)
              if p != A.final and A.labels[p] != A.labels[q]]
    edges={v:[] for v in vertices}; rev={v:[] for v in vertices}
    for p,q in vertices:
        for a in range(A.alphabet):
            u,v=A.delta[p][a], A.delta[q][a]
            if min(u,v)<0 or u == A.final or A.labels[u] == A.labels[v]: continue
            edges[p,q].append(((u,v),a)); rev[u,v].append((p,q))
    ends=[v for v in vertices if v[1] == A.final]
    productive=set(ends); todo=list(ends)
    for v in todo:
        for u in rev[v]:
            if u not in productive: productive.add(u); todo.append(u)
    roots=sorted((p,q) for p,q in productive if A.labels[q] == target
                 and (A.labels[p],target) in flags)
    parents={v:None for v in roots}; queue=deque(roots)
    bad=None
    while queue:
        p,q=queue.popleft()
        if A.labels[q] == target and (A.labels[p],target) not in flags:
            bad=(p,q); break
        for nxt,a in edges[p,q]:
            if nxt in productive and nxt not in parents:
                parents[nxt]=((p,q),a); queue.append(nxt)
    if bad is None:
        return dict(status='CLOSED', target=target, domain=A.digest(),
                    productive=[list(v) for v in sorted(productive)],
                    reachable=[list(v) for v in sorted(parents)])
    word=[]; at=bad
    while parents[at] is not None: at,a=parents[at]; word.append(a)
    return dict(status='UNKNOWN', target=target, domain=A.digest(),
                obstruction=dict(root=at, endpoint=bad, word=tuple(reversed(word)),
                meaning='Productive synchronized-return path; not necessarily one-word realizable'))


def tail_patterns(A: Domain, target_states, limits=Limits()):
    """All tails after a LAST target, or a productive target-free cycle.

    Returns a finite complete list of (anchor state, tail word) only after
    proving acyclicity. A cap never returns a partial list as a complete cover.
    """
    T=set(target_states)
    allowed=set(range(A.k))-T
    rev={p:[] for p in allowed}
    adj={p:[] for p in allowed}
    for p in allowed:
        for a,q in enumerate(A.delta[p]):
            if q in allowed: adj[p].append((q,a)); rev[q].append(p)
    productive={A.final}; todo=[A.final]
    for p in todo:
        for q in rev[p]:
            if q not in productive: productive.add(q); todo.append(q)
    # Detect productive cycles reachable from any last-target first step.
    access=set(); queue=[]
    for t in sorted(T):
        for q in A.delta[t]:
            if q in productive and q not in access: access.add(q); queue.append(q)
    for p in queue:
        for q,a in adj[p]:
            if q in productive and q not in access: access.add(q); queue.append(q)
    indeg={p:0 for p in access}
    for p in access:
        for q,a in adj[p]:
            if q in access: indeg[q]+=1
    ready=deque(sorted(p for p in access if not indeg[p])); order=[]
    while ready:
        p=ready.popleft(); order.append(p)
        for q,a in adj[p]:
            if q in indeg:
                indeg[q]-=1
                if not indeg[q]:ready.append(q)
    if len(order)<len(access):
        # Iterative three-color DFS identifies a genuine cycle vertex, not
        # merely a descendant retained by Kahn's elimination.
        color={}; found=None
        for root in sorted(access):
            if color.get(root):continue
            color[root]=1; stack=[(root,0)]
            while stack and found is None:
                p,index=stack[-1]
                if index==len(adj[p]):
                    color[p]=2;stack.pop();continue
                stack[-1]=(p,index+1);q,a=adj[p][index]
                if q not in access:continue
                if color.get(q)==1:found=q;break
                if not color.get(q):color[q]=1;stack.append((q,0))
            if found is not None:break
        assert found is not None
        for t in sorted(T):
            starts=[q for q in A.delta[t] if q in productive]
            seen=set(starts); pending=list(starts)
            for p in pending:
                for q,a in adj[p]:
                    if q in productive and q not in seen:seen.add(q);pending.append(q)
            if found in seen:return dict(kind='INFINITE',anchor=t)
        raise AssertionError('Lost productive cycle anchor')
    suffixes={}
    for p in reversed(order):
        vals=[()] if p==A.final else []
        for q,a in adj[p]:
            if q in suffixes:
                vals.extend((a,)+w for w in suffixes[q])
                if limits.patterns is not None and len(vals)>limits.patterns:
                    raise Capped('finite-tail pattern cap')
        suffixes[p]=vals
    patterns=[]
    for t in sorted(T):
        for a,q in enumerate(A.delta[t]):
            for v in suffixes.get(q,[]):
                patterns.append((t,(a,)+v))
                if limits.patterns is not None and len(patterns)>limits.patterns:
                    raise Capped('finite-tail pattern cap')
    return dict(kind='FINITE',patterns=patterns)


def long_tail_witness(A: Domain, target_states, anchor: int, limits=Limits()):
    X=shortest(A,A.start,lambda p:p==anchor)
    assert X is not None
    threshold=A.k*len(X); T=set(target_states)
    start=(anchor,0); queue=deque([start]); parent={start:None}; found=None
    while queue:
        p,d=queue.popleft()
        if p==A.final and d==threshold:found=(p,d);break
        for a,q in enumerate(A.delta[p]):
            if q<0 or q in T:continue
            nxt=(q,min(threshold,d+1))
            if nxt not in parent:
                if limits.states is not None and len(parent)>=limits.states:
                    raise Capped('long-tail search state cap')
                parent[nxt]=((p,d),a);queue.append(nxt)
    assert found is not None
    Y=[]
    while parent[found] is not None:found,a=parent[found];Y.append(a)
    Y=tuple(reversed(Y)); w=X+Y
    assert A.accepts(w) and len(w)<=A.k*A.k+A.k-2
    assert all(w[i:i+len(Y)]!=Y for i in range(len(X)))
    return w


def fixed_tail_filter(A: Domain, flags, anchor: int, Y: Word, limits=Limits()):
    """Require terminal Y from anchor; forbid Y only at this column's sources.

    At most K*len(Y)+1 states BEFORE trimming. Memory (ell,p) stores the
    original-domain state p at the start of the longest matching proper prefix
    of Y; the current domain state is delta(p,Y[:ell]). Shorter suffix starts
    are obtained by deterministic propagation, not independent word choices.
    """
    Y=tuple(Y); m=len(Y)
    if not m:raise ValueError('Nonempty tail required')
    run=A.run(Y,anchor)
    if run is None or run[-1]!=A.final:raise ValueError('Tail must accept from anchor')
    t=A.labels[anchor]
    prefix=[]
    for p in range(A.k):
        path=[p]
        for a in Y:
            q=path[-1]
            path.append(A.delta[q][a] if q>=0 else -1)
        prefix.append(path)
    # Transition of the longest matched proper prefix, including complete hits.
    move=[]
    for ell in range(m):
        row=[]
        for a in range(A.alphabet):
            z=Y[:ell]+(a,)
            length=max(h for h in range(min(m,len(z))+1)
                       if h==0 or z[-h:]==Y[:h])
            row.append(length)
        move.append(row)
    border=max(h for h in range(m) if h==0 or Y[-h:]==Y[:h])
    keys=[(0,A.start)];ids={keys[0]:0};rows=[];labels=[]; final=-1
    at=0
    while at<len(keys):
        key=keys[at]
        if key is None:
            rows.append(tuple(-1 for _ in range(A.alphabet)))
            labels.append(A.labels[A.final]);final=at;at+=1;continue
        ell,p=key; q=prefix[p][ell]
        assert q>=0
        labels.append(A.labels[q]); row=[]
        for a,r in enumerate(A.delta[q]):
            if r<0:row.append(-1);continue
            h=move[ell][a]; shift=ell+1-h
            # The shifted start lies in the old matching prefix unless the
            # new longest match is empty, in which case it is the current r.
            p2=r if h==0 else prefix[p][shift]
            assert p2>=0
            hit=h==m
            if hit and (A.labels[p2],t) in flags:
                row.append(-1);continue
            if r==A.final:
                if hit and p2==anchor:nxt=None
                else:row.append(-1);continue
            else:
                if hit:p2=prefix[p2][m-border];h=border
                assert p2>=0 and prefix[p2][h]==r
                nxt=(h,p2)
            if nxt not in ids:
                if limits.states is not None and len(keys)>=limits.states:
                    raise Capped('fixed-tail filter state cap')
                ids[nxt]=len(keys);keys.append(nxt)
            row.append(ids[nxt])
        rows.append(tuple(row));at+=1
    assert len(rows)<=A.k*m+1
    if final<0:return None
    return trim(Domain(tuple(rows),0,final,tuple(labels)))


def filtered_spec(A: Domain, flags, anchor, Y, w):
    """Literal all-cuts specification, deliberately independent of KMP state."""
    c=A.run(tuple(w)); Y=tuple(Y);m=len(Y)
    if c is None or c[-1]!=A.final or len(w)<m:return False
    j=len(w)-m
    if c[j]!=anchor or tuple(w[j:])!=Y:return False
    t=A.labels[anchor]
    return all((A.labels[c[i]],t) not in flags or tuple(w[i:i+m])!=Y
               for i in range(len(w)-m+1))


def last_columns_spec(A: Domain, flags, targets, w):
    c=A.run(tuple(w))
    if c is None or c[-1]!=A.final:return False
    for t in targets:
        cuts=[j for j,q in enumerate(c) if A.labels[q]==t]
        if not cuts:continue
        j=cuts[-1]; Y=tuple(w[j:])
        if any((A.labels[c[i]],t) in flags and tuple(w[i:i+len(Y)])==Y for i in range(j)):
            return False
    return True


def domain_witness(A: Domain, flags, targets, w):
    c=A.run(tuple(w))
    if c is None or c[-1]!=A.final:return False
    return all(A.labels[c[j]] not in targets or
               (A.labels[c[i]],A.labels[c[j]]) not in flags or
               tuple(w[i:i+len(w)-j])!=tuple(w[j:])
               for i in range(len(c)) for j in range(i,len(c)))


def solve_domain(A: Domain, flags, targets, limits=Limits(), stats=None):
    if stats is None:stats=dict(nodes=0,max_states=0,filters=0,eliminations=0,cycles=0)
    stats['nodes']+=1;stats['max_states']=max(stats['max_states'],A.k)
    if limits.nodes is not None and stats['nodes']>limits.nodes:raise Capped('recursive-node cap')
    T=set(targets)&set(A.labels)
    tstates={q for q,t in enumerate(A.labels) if t in T}
    free=shortest(A,A.start,lambda p:p==A.final,lambda p:p not in tstates)
    if free is not None:
        return dict(status='YES',word=free,reason='no remaining target',targets=sorted(T),domain=A.digest())
    info=tail_patterns(A,tstates,limits)
    if info['kind']=='INFINITE':
        w=long_tail_witness(A,tstates,info['anchor'],limits);stats['cycles']+=1
        return dict(status='YES',word=w,reason='productive target-free tail cycle',
                    targets=sorted(T),domain=A.digest())
    branches=[];unknown=False
    for anchor,Y in info['patterns']:
        branch=dict(anchor=anchor,tail=Y,target=A.labels[anchor])
        try:
            B=fixed_tail_filter(A,flags,anchor,Y,limits);stats['filters']+=1
            if B is None:
                branch.update(status='NO',reason='empty fixed-tail filter');branches.append(branch);continue
            # Certification AFTER restricting the whole word can be stronger
            # than original closure. It never licenses an uncertified deletion.
            cert=return_certificate(B,flags,A.labels[anchor],limits)
            branch['return_certificate']=cert
            if cert['status']!='CLOSED':
                branch.update(status='UNKNOWN',reason='return closure not certified');unknown=True
                branches.append(branch);continue
            stats['eliminations']+=1
            child=solve_domain(B,flags,T-{A.labels[anchor]},limits,stats)
            branch.update(status=child['status'],child=child)
            if child['status']=='YES':
                w=tuple(child['word'])
                assert A.accepts(w) and domain_witness(A,flags,T,w)
                return dict(status='YES',word=w,reason='source-sensitive target elimination',
                            domain=A.digest(),targets=sorted(T),chosen=branch)
            if child['status']=='UNKNOWN':unknown=True
        except (Capped, RecursionError) as exc:
            reason='host recursion limit' if isinstance(exc,RecursionError) else str(exc)
            branch.update(status='UNKNOWN',reason=reason);unknown=True
        branches.append(branch)
    return dict(status='UNKNOWN' if unknown else 'NO',domain=A.digest(),
                targets=sorted(T),branches=branches,reason='finite-tail branch exhaustion')


def solve(I: Instance, limits=Limits()):
    stats=dict(nodes=0,max_states=0,filters=0,eliminations=0,cycles=0)
    slices=[];unknown=False
    for f in sorted(I.finals):
        norm=normalize(I,f)
        if norm is None:
            slices.append(dict(final=f,status='NO',reason='empty boundary slice'));continue
        J,order=norm
        A=Domain(J.delta,J.start,next(iter(J.finals)),tuple(range(J.k)))
        T={t for p,t in J.flags}
        try:out=solve_domain(A,J.flags,T,limits,stats)
        except (Capped, RecursionError) as exc:
            out=dict(status='UNKNOWN',reason='host recursion limit' if isinstance(exc,RecursionError) else str(exc))
        record=dict(final=f,normalization=list(order),result=out,status=out['status'])
        slices.append(record)
        if out['status']=='YES':
            w=tuple(out['word'])
            assert witness(I,w) and reverse_witness(I,w)
            return dict(status='YES',word=w,stats=stats,slices=slices)
        unknown|=out['status']=='UNKNOWN'
    return dict(status='UNKNOWN' if unknown else 'NO',stats=stats,slices=slices)


def original_closed_columns(I,limits=Limits()):
    out=[]
    for f in sorted(I.finals):
        norm=normalize(I,f)
        if norm is None:continue
        J,_=norm;A=Domain(J.delta,J.start,next(iter(J.finals)),tuple(range(J.k)))
        certs=[return_certificate(A,J.flags,t,limits) for t in sorted({t for p,t in J.flags})]
        out.append(dict(final=f,all_closed=all(c['status']=='CLOSED' for c in certs),certificates=certs))
    return out


def from_json(d):
    return Instance(tuple(tuple(r) for r in d['delta']),d.get('start',0),
                    frozenset(d['finals']),frozenset(tuple(p) for p in d.get('flags',[])),
                    frozenset(d.get('bad',[])))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path,help='Terminal instance JSON')
    p.add_argument('--output',type=Path)
    p.add_argument('--uncapped',action='store_true',help='Disable resource caps; closure failures remain UNKNOWN')
    args=p.parse_args()
    if not __debug__:p.error('Run without python -O; certificate assertions must execute')
    I=from_json(json.loads(args.input.read_text()))
    limits=Limits(None,None,None,None) if args.uncapped else Limits()
    out=solve(I,limits)
    text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text)

if __name__=='__main__':main()

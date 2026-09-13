#!/usr/bin/env python3
"""Exact C075 scheme cost for a family derived from C048/C050.

The synchronization construction is prior repository work. The new invariant
is same-phase counter-window injectivity, preventing any repeated source loop.
Not a general subtype-entailment decision. Python 3.10+, standard library only.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import argparse, json, random
from suffix_switch import DFA, Instance, universal, witness_direct, witness_reverse
BASE = '4ce1d6b5d20d3fa39a5c4f72d9c96da24e56356a'


def build_machine(start, step, accepting):
    states=[start]; ids={start:0}; rows=[]; finals=set()
    for s in states:
        if accepting(s): finals.add(ids[s])
        row=[]
        for a in (0,1):
            t=step(s,a)
            if t is None: row.append(-1); continue
            if t not in ids: ids[t]=len(states); states.append(t)
            row.append(ids[t])
        rows.append(tuple(row))
    return DFA(tuple(rows),0,frozenset(finals))


def counter_word(d):
    if type(d) is not int or d<1: raise ValueError('Positive integer width required')
    return tuple((n>>j)&1 for n in range(1<<d) for j in range(d))


def counter_automata(d):
    if type(d) is not int or d<1: raise ValueError('Positive integer width required')
    def fmt(s,a):
        if s[0]=='final': return None
        if s[0]=='first':
            if a: return None
            return ('first',s[1]+1) if s[1]+1<d else ('block',0,True)
        _,pos,ones=s; ones=ones and bool(a)
        if pos+1<d: return ('block',pos+1,ones)
        return ('final',) if ones else ('block',0,True)
    ds=[build_machine(('first',0),fmt,lambda s:s[0]=='final')]
    for j in range(d):
        def step(s,a,j=j):
            pos,e,carry=s
            if pos<j: carry=carry and bool(a)
            if pos==j:
                if e is not None and a!=e: return None
                e=a^int(carry)
            return (0,e,True) if pos+1==d else (pos+1,e,carry)
        ds.append(build_machine((0,None,True),step,lambda s:s[0]==0 and s[1] is not None))
    return tuple(ds)


def intersection_shortest(ds):
    start=tuple(d.start for d in ds); todo=deque([start]); parent={start:None}
    while todo:
        s=todo.popleft()
        if all(p in d.finals for d,p in zip(ds,s)):
            w=[]
            while parent[s] is not None: s,a=parent[s]; w.append(a)
            return tuple(reversed(w)),len(parent)
        for a in (0,1):
            t=tuple(d.delta[p][a] for d,p in zip(ds,s))
            if min(t)<0: continue
            if t not in parent: parent[t]=(s,a); todo.append(t)
    return None,len(parent)


@dataclass(frozen=True)
class Sync:
    instance: Instance
    inputs: tuple[DFA,...]
    entries: tuple[int,...]
    boundaries: tuple[dict[tuple[int,int],int],...]


def compile_sync(ds):
    if len(ds)<2 or any(d.alphabet!=2 for d in ds): raise ValueError('Need at least two binary DFAs')
    rows=[]; tags=[]; entries=[]; bounds=[]; helpers=[]; separators=[]
    def new(tag=None):
        q=len(rows); rows.append([-1,-1]); tags.append(tag); return q
    for i,d in enumerate(ds):
        entries.append(new((i,2)))  # predecessor tag 2 denotes START
        bounds.append({(q,a):new((i,a)) for q in range(d.n) for a in (0,1)})
        helpers.append([new() for _ in range(d.n)]); separators.append(new())
    final=new()
    for i,d in enumerate(ds):
        for q in range(d.n):
            for a in (0,1):
                if d.delta[q][a]>=0: rows[helpers[i][q]][a]=bounds[i][d.delta[q][a],a]
        for p,q in [(entries[i],d.start)]+[(p,q) for (q,a),p in bounds[i].items()]:
            rows[p][1]=helpers[i][q]
            if q in d.finals: rows[p][0]=separators[i]
        rows[separators[i]][0]=entries[i+1] if i+1<len(ds) else final
    sources=[(p,t) for p,t in enumerate(tags) if t is not None and t[0]<len(ds)-1]
    targets=[(p,t) for p,t in enumerate(tags) if t is not None and t[0]==len(ds)-1]
    flags=frozenset((p,q) for p,s in sources for q,t in targets if s[1]!=t[1])
    return Sync(Instance(DFA(tuple(map(tuple,rows)),entries[0],frozenset({final})),flags),
                tuple(ds),tuple(entries),tuple(bounds))


def encode_data(u): return tuple(b for a in u for b in (1,a))
def candidate(us): return sum((encode_data(u)+(0,0) for u in us),())


def z_values(w):
    """Exact Z algorithm. No hashing."""
    n=len(w); z=[0]*n; l=r=0
    for i in range(1,n):
        if i<r: z[i]=min(r-i,z[i-l])
        while i+z[i]<n and w[z[i]]==w[i+z[i]]: z[i]+=1
        if i+z[i]>r: l,r=i,i+z[i]
    if n: z[0]=n
    return z


def witness_z(I,w):
    c=I.machine.run(w)
    if c is None or c[-1] not in I.machine.finals: return False
    pred={}
    for p,t in I.flags: pred.setdefault(t,set()).add(p)
    for j,t in enumerate(c):
        if t not in pred: continue
        v=w[j:]; L=len(v)
        if not L:
            if any(p in pred[t] for p in c[:j+1]): return False
        else:
            z=z_values(v+(-1,)+w)
            if any(c[i] in pred[t] and z[L+1+i]>=L for i in range(j+1)): return False
    return True


def witness_kmp(I,w):
    """Independent reversed-prefix failure-link oracle."""
    c=I.machine.run(w)
    if c is None or c[-1] not in I.machine.finals: return False
    x=w[::-1]; states=c[::-1]; pi=[0]*len(x)
    for i in range(1,len(x)):
        j=pi[i-1]
        while j and x[i]!=x[j]: j=pi[j-1]
        if x[i]==x[j]: j+=1
        pi[i]=j
    for e in range(len(x)+1):
        b=e
        while True:
            if (states[e],states[b]) in I.flags: return False
            if not b: break
            b=pi[b-1]
    return True


def source_cuts(I,w):
    c=I.machine.run(w)
    if c is None or c[-1] not in I.machine.finals: raise ValueError('Accepted word required')
    S={p for p,t in I.flags}
    return c,[i for i,p in enumerate(c) if p in S]


def minimum_scheme_cost(I,w):
    """Exact C075 syntactic cost for ONE accepted word, not witness synthesis."""
    c,cuts=source_cuts(I,w); n=len(cuts); dp=[0]*(n+1); choice=[None]*n
    for i in range(n-1,-1,-1):
        dp[i]=1+dp[i+1]; choice[i]=(i,0,0)
        start=cuts[i]; z=z_values(w[start:])
        for j in range(i+1,n):
            if c[cuts[j]]!=c[start]: continue
            length=cuts[j]-start; d=j-i
            copies=1+(z[length]//length if length<len(z) else 0)
            # One-copy phases have the same cost as their individual plain visits.
            for m in range(2,copies+1):
                end=i+m*d
                assert end<n and cuts[end]==start+m*length
                cost=1+d+dp[end+1]
                if cost<dp[i]: dp[i]=cost; choice[i]=(end,d,m)
    phases=[]; i=0
    while i<n:
        end,d,m=choice[i]
        phases.append(dict(start=cuts[i],base_end=cuts[i+d],end=cuts[end],arrivals=d,copies=m))
        i=end+1
    out=dict(cost=dp[0],source_visits=n,phases=phases)
    verify_certificate(I,w,out)
    return out


def verify_certificate(I,w,out):
    """Independent concrete partition verifier; does not assert minimality."""
    c,cuts=source_cuts(I,w); S={p for p,t in I.flags}; used=[]; cost=0
    for p in out['phases']:
        a,b,e,d,m=(p[x] for x in ('start','base_end','end','arrivals','copies'))
        assert len(used)<len(cuts) and a==cuts[len(used)] and c[a]==c[e]
        if m:
            assert a<b<=e and c[b]==c[a] and w[a:e]==w[a:b]*m
            assert d==sum(c[t] in S for t in range(a+1,b+1)) and d>0
        else: assert a==b==e and d==0
        used.extend(t for t in range(a,e+1) if c[t] in S); cost+=1+d
    assert used==cuts and cost==out['cost'] and len(cuts)==out['source_visits']


def live_source_certificates(S,u):
    """Every visited source has an actual bad accepted-word comparison."""
    U=S.inputs[-1]
    if U.delta!=((0,0),) or U.finals!=frozenset({0}): raise ValueError('Universal last component required')
    I=S.instance; r=len(S.inputs); blocklen=2*len(u)+2
    c,cuts=source_cuts(I,candidate([u]*r)); needed={c[t] for t in cuts}; seen=set(); certs=[]
    for stage in range(r-1):
        path=S.inputs[stage].run(u); assert path is not None
        for t in range(len(u)+1):
            p=S.entries[stage] if t==0 else S.boundaries[stage][path[t],u[t-1]]
            if p in seen: continue
            master=(0,)+u if t==0 else u[t:]
            w=candidate([u]*(r-1)+[master]); run=I.machine.run(w)
            a=stage*blocklen+2*t; b=(r-1)*blocklen+(2 if t==0 else 0)
            assert run is not None and run[-1] in I.machine.finals
            assert run[a]==p and (p,run[b]) in I.flags and w[a:a+len(w)-b]==w[b:]
            seen.add(p)
            certs.append(dict(source=p,target=run[b],stage=stage,data_cut=t,
                              master=list(master),source_cut=a,target_cut=b))
    assert seen==needed
    return certs


def self_test():
    rng=random.Random(2026091361); rows=[]; counts=dict(common_words=0,corruptions=0,live_sources=0)
    for d in range(1,7):
        ds=counter_automata(d); u=counter_word(d)
        assert sum(M.n for M in ds)<=6*d*d+3*d
        shortest,product_states=intersection_shortest(ds); assert shortest==u
        for i in range(len(u)):
            v=u[:i]+(1-u[i],)+u[i+1:]
            assert not all(M.accepts(v) for M in ds); counts['corruptions']+=1
        S=compile_sync(ds+(universal(2),)); I=S.instance; w=candidate([u]*len(S.inputs))
        assert I.machine.n==3*sum(M.n for M in S.inputs)+2*len(S.inputs)+1
        assert I.machine.n<=18*d*d+11*d+8
        assert witness_z(I,w) and witness_kmp(I,w)
        if d<=3: assert witness_direct(I,w) and witness_reverse(I,w)
        certs=live_source_certificates(S,u); counts['live_sources']+=len(certs)
        cost=minimum_scheme_cost(I,w)
        assert cost['cost']==cost['source_visits']==(d+1)*(d*(1<<d)+1)
        rows.append(dict(width=d,states=I.machine.n,flags=len(I.flags),witness_bits=len(w),
                         product_states=product_states,scheme=cost,live_certificates=certs))
        if d<=2:
            for n in range(len(u)+1):
                for v in product((0,1),repeat=n):
                    assert all(M.accepts(v) for M in ds)==(v==u); counts['common_words']+=1
    counts['four_predicate_comparisons']=0
    for _ in range(160):
        n=rng.randint(2,7)
        delta=tuple(tuple(rng.randrange(-1,n) for _ in range(2)) for _ in range(n-1))+((-1,-1),)
        G=frozenset((p,t) for p in range(n) for t in range(n) if rng.random()<.2)
        I=Instance(DFA(delta,0,frozenset({n-1})),G)
        for length in range(7):
            for w in product((0,1),repeat=length):
                assert witness_direct(I,w)==witness_reverse(I,w)==witness_z(I,w)==witness_kmp(I,w)
                counts['four_predicate_comparisons']+=1
    counts['phase_windows']=0; counts['phase_automata']=0
    for d in range(1,10):
        u=counter_word(d)
        for t in range(d):
            seen=set()
            for start in range(t,len(u)-d+1,d):
                window=u[start:start+d]; assert window not in seen; seen.add(window)
                high=sum(a<<i for i,a in enumerate(window[:d-t]))
                low=sum(a<<i for i,a in enumerate(window[d-t:]))
                value=(high<<t)+((low-1)%(1<<t)) if t else high
                assert value==start//d; counts['phase_windows']+=1
        for M in counter_automata(d):
            phases={M.start:0}; queue=[M.start]
            for p in queue:
                for q in M.delta[p]:
                    if q<0: continue
                    phase=(phases[p]+1)%d
                    if q in phases: assert phases[q]==phase
                    else: phases[q]=phase; queue.append(q)
            assert len(phases)==M.n; counts['phase_automata']+=1
    return dict(status='PASS',base_commit=BASE,seed=2026091361,counts=counts,families=rows,
                scope='Exact C075 cost for the stated singleton family, not general decision',
                evidence='Written proof and finite checks; independent review pending, not Lean')


def compact(out):
    return {**{k:v for k,v in out.items() if k!='families'},
            'families':[dict(width=r['width'],states=r['states'],flags=r['flags'],
                             witness_bits=r['witness_bits'],exact_scheme_cost=r['scheme']['cost'],
                             live_sources=len(r['live_certificates'])) for r in out['families']]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test',action='store_true'); parser.add_argument('--output',type=Path)
    parser.add_argument('--full-output',type=Path); args=parser.parse_args()
    if not args.self_test or not __debug__: parser.error('Use --self-test without Python -O')
    out=self_test(); small=compact(out)
    if args.output: args.output.write_text(json.dumps(small,indent=2,sort_keys=True)+'\n')
    if args.full_output: args.full_output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(small,indent=2,sort_keys=True))

if __name__=='__main__': main()

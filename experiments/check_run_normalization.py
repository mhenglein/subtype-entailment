"""E035: symbolic terminal profiles, normalization, and bounded-run checks.

Quantified claims rest on the written proof, not these finite experiments.
"""
from collections import deque
from dataclasses import replace
from itertools import product
from pathlib import Path
import hashlib,json,random
from border_lab import Instance,words,witness,border_witness
from run_normalization import *
from run_bound_decision import verify_runs,solve_run_bound,compile_unary_sync
from word_sync import BinaryDFA,encode_blocks
from counter_intersection import counting_word
from denial_bridge import Canonical
from terminal_realization import realize

ROOT=Path(__file__).resolve().parents[1]


def reverse_profile(I,w):
    c=I.run(w)[::-1];u=w[::-1]
    return frozenset((c[m],c[b]) for m in range(len(u)+1) for b in range(m+1) if u[:b]==u[m-b:m])


def shortest_suffix(I,start):
    todo=deque([(start,'')]);seen={start}
    while todo:
        q,w=todo.popleft()
        if q in I.final:return w
        for a,t in enumerate(I.delta[q]):
            if t>=0 and t not in seen:seen.add(t);todo.append((t,w+str(a)))
    return None


def check():
    rng=random.Random(2026090654)
    C=dict(three_state_tables=0,short_accepted_words=0,random_profile_words=0,
           transformations=0,gap_comparisons=0,tail_trace_comparisons=0,
           long_profile_words=0,huge_encoded_words=0,strict_compressions=0,
           finite_run_oracles=0,finite_run_queries=0,unary_intersections=0,
           unary_block_vectors=0,canonical_models=0,counting_fixtures=0,caps=0)
    small=tuple(words('01',7))
    for flat in product(range(-1,3),repeat=4):
        I=Instance((flat[:2],flat[2:],(-1,-1)),frozenset({2}));C['three_state_tables']+=1
        for w in small:
            if not I.admissible(w):continue
            p=profile_direct(I,w)
            assert p==reverse_profile(I,w)==profile_runs(I,rle(w))
            out=normalize(I,rle(w));assert profile_direct(I,expand(out['runs']))==p
            C['short_accepted_words']+=1
    for _ in range(450):
        k=rng.randrange(2,9)
        I=Instance(tuple(tuple(rng.randrange(-1,k) for a in '01') for q in range(k-1))+((-1,-1),),frozenset({k-1}))
        for w in words('01',7):
            if I.admissible(w):
                p=profile_direct(I,w);assert p==reverse_profile(I,w)==profile_runs(I,rle(w))
                C['random_profile_words']+=1
    for k in range(1,5):
        for trans in product(range(k),repeat=k):
            I=Instance(tuple((-1,q) for q in trans),frozenset())
            u=unary(I,'1');H=(k+1)**2;P=u.global_period;C['transformations']+=1
            for trial in range(6):
                vals=[0,1,H,H+1,H+P+3,H+2*P+7]+[rng.randrange(1,4*H+20) for _ in range(3)]
                m=count_map(vals,H,P)
                for x,y in product(set(vals),repeat=2):
                    d=abs(x-y);e=abs(m[x]-m[y])
                    assert (d==e if d<=H else e>H)
                    assert (x-y-m[x]+m[y])%P==0 and (x<y)==(m[x]<m[y])
                    C['gap_comparisons']+=1
                for p,q in product(range(k),repeat=2):
                    x,y=rng.choice(vals[1:]),rng.choice(vals[1:])
                    brute=frozenset((u.power(p,x-t),u.power(q,y-t)) for t in range(1,min(x,y)+1))
                    assert brute==pair_tail_states(u,p,q,x,y)==pair_tail_states(u,p,q,m[x],m[y])
                    C['tail_trace_comparisons']+=1
    for huge,trials in ((False,1600),(True,1200)):
        for _ in range(trials):
            k=rng.randrange(3,10)
            I=Instance(tuple(tuple(rng.randrange(-1,k) for a in '01') for q in range(k-1))+((-1,-1),),frozenset({k-1}))
            ops=tuple(unary(I,a) for a in '01');prefix=[];q=I.start;last=None
            for step in range(rng.randrange(1,7)):
                a=rng.choice('01') if last is None else str(1-int(last))
                n=(10**rng.randrange(25,90)+rng.randrange(100)) if huge else rng.randrange(1,90)
                t=ops[int(a)].power(q,n)
                if t==k or t==k-1:break
                prefix.append((a,n));q=t;last=a
            if not prefix:continue
            end=shortest_suffix(I,q)
            if end is None:continue
            runs=list(prefix)
            for a in end:
                if runs and runs[-1][0]==a:runs[-1]=(a,runs[-1][1]+1)
                else:runs.append((a,1))
            runs=tuple(runs)
            try:out=normalize(I,runs)
            except ValueError:continue
            p=profile_runs(I,runs)
            J=replace(I,flags=frozenset((x,y) for x in range(k) for y in range(k) if (x,y) not in p))
            assert verify_runs(J,runs) and verify_runs(J,out['runs']) and len(out['runs'])==len(runs)
            C['strict_compressions']+=out['normalized_length']<out['original_length']
            if huge:C['huge_encoded_words']+=1
            else:
                w=expand(runs);v=expand(out['runs'])
                assert profile_direct(I,w)==p==profile_direct(I,v)
                assert witness(J,w) and border_witness(J,w) and witness(J,v) and border_witness(J,v)
                C['long_profile_words']+=1
    run_verdicts={s:0 for s in ('YES','NO_WITHIN_RUN_BOUND','UNKNOWN')}
    for _ in range(120):
        k=rng.randrange(2,7)
        D=tuple(tuple(rng.choice([-1]+list(range(q+1,k))) for a in '01') for q in range(k-1))+((-1,-1),)
        G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.07)
        I=Instance(D,frozenset({k-1}),G)
        candidates=[w for w in words('01',k-1) if witness(I,w)];C['finite_run_oracles']+=1
        for R in (0,1,2,3):
            out=solve_run_bound(I,R,max_prefixes=None,max_count_entries=None)
            expected=any(len(rle(w))<=R for w in candidates)
            assert (out['status']=='YES')==expected and out['status']!='UNKNOWN'
            C['finite_run_queries']+=1;run_verdicts[out['status']]+=1
    ms=[]
    for f in product(range(-1,2),repeat=2):
        for mask in range(4):ms.append(BinaryDFA(((-1,f[0]),(-1,f[1])),frozenset(q for q in range(2) if mask>>q&1)))
    unary_counts={'YES':0,'NO':0}
    for M,N in product(ms,repeat=2):
        I,R=compile_unary_sync((M,N))
        common=[n for n in range(1,5) if M.accepts('1'*n) and N.accepts('1'*n)]
        unary_counts['YES' if common else 'NO']+=1
        for x,y in product(range(1,5),repeat=2):
            w='1'*x+'0'+'1'*y+'0'
            expected=x==y and M.accepts('1'*x) and N.accepts('1'*y)
            assert witness(I,w)==border_witness(I,w)==verify_runs(I,rle(w))==expected
            C['unary_block_vectors']+=1
        C['unary_intersections']+=1
    I=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}))
    N=10**80;big=(('1',N),('0',1),('1',N+1),('0',1));compressed=normalize(I,big)
    bad=(('1',37),('0',1),('1',37),('0',1))
    assert (0,2) not in profile_runs(I,big) and (0,2) in profile_runs(I,bad)
    p=profile_runs(I,big)
    J=replace(I,flags=frozenset((a,b) for a in range(5) for b in range(5) if (a,b) not in p))
    R=realize(J)
    assert not Canonical(R.variables,R.constraints,R.alpha,R.beta,expand(compressed['runs'])).errors()
    C['canonical_models']+=1;assert not verify_runs(J,bad)
    assert Canonical(R.variables,R.constraints,R.alpha,R.beta,expand(bad)).errors();C['canonical_models']+=1
    guard=Instance(((1,-1),(-1,2),(-1,3),(4,-1),(-1,5),(-1,-1)),frozenset({5}))
    assert guard.admissible('01101') and (0,3) in profile_direct(guard,'01101')
    assert profile_direct(guard,'01101')==profile_runs(guard,rle('01101'))
    counts=[]
    for d in range(1,7):
        u=counting_word(d);w=encode_blocks([u]*(d+1));actual=len(rle(w));expected=(d+1)*(d*(1<<d)+2)
        assert actual==expected;C['counting_fixtures']+=1
        counts.append(dict(width=d,run_count=actual,word_length=len(w)))
    cap=solve_run_bound(J,4,max_prefixes=1)
    assert cap['status']=='UNKNOWN';C['caps']+=1
    try:expand(big);raise AssertionError('Expansion cap was ignored')
    except ValueError:pass
    assert solve_run_bound(I,0)['status']=='NO_WITHIN_RUN_BOUND'
    assert count_map(iter([100,101]),36,1)=={0:0,100:37,101:38}
    def blob(p):
        b=p.read_bytes();return hashlib.sha1(('blob %d\0'%len(b)).encode()+b).hexdigest()
    return dict(status='PASS',seed=2026090654,counts=C,run_bound_verdicts=run_verdicts,
                unary_intersection_oracles=unary_counts,
                huge_fixture={k:v for k,v in compressed.items() if k!='maps'},
                independent_compression_counterexample=dict(bad_runs=bad,new_pair=(0,2)),
                final_partial_run_fixture='01101',counting_run_lower_bound=counts,cap=cap,
                scope='Universal terminal-word normalization; bounded-run decision only',
                proof_status='Written proof; not Lean-checked or independently reviewed',
                dependency_blobs={p:blob(ROOT/'experiments'/p) for p in ('border_lab.py','terminal_realization.py','denial_bridge.py')})

if __name__=='__main__':
    out=check();(ROOT/'results'/'run-normalization.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

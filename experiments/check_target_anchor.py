#!/usr/bin/env python3
"""Finite falsification, complete small oracles, and independent NO replay.
All global claims require the accompanying ordinary proof. Complete bounded
oracles invoke the proved class bound, not an observed cutoff. Python 3.10+.
"""
from __future__ import annotations
from collections import Counter, deque
from itertools import product
from pathlib import Path
import argparse, copy, json, random
from target_anchor import (Instance,FIXTURES,normalize,color_certificate,encode,
    witness,reverse_witness,anchored_word_test,compile_anchor,compiled_word_test,
    solve_columns,solve,solve_with_tail_test,generic_unique_tail,kmp_avoid,
    certificate_json,from_json)
BASE='c4f7e56665828710b3bda77e32bb2904ad4006d6'
SEED=20260913122


def words(alphabet,n):
    for k in range(n+1):yield from product(range(alphabet),repeat=k)


def accepted_paths(I,bound):
    queue=deque([(I.start,())])
    while queue:
        p,w=queue.popleft()
        if p in I.bad:continue
        if p in I.finals:yield w
        if len(w)==bound:continue
        for a,q in enumerate(I.delta[p]):
            if q>=0:queue.append((q,w+(a,)))


def oracle_shortest(I,bound):
    for w in accepted_paths(I,bound):
        if reverse_witness(I,w):return w
    return None


def independent_column_no(J,answer):
    """Replay NO without KMP, reach(), or tail_analysis().
    Check target-free reachability; enumerate ALL last-target tails with explicit
    cycle detection; verify supplied prefix-product closure by LITERAL suffixes.
    A productive last-target cycle makes a claimed NO invalid.
    """
    assert answer['status']=='NO'
    T={t for p,t in J.flags};f=next(iter(J.finals))
    assert J.flags=={(p,t) for t in T for p in range(J.k) if p!=t and p!=f}
    if J.start not in T:
        seen={J.start};todo=[J.start]
        for p in todo:
            assert p!=f
            for q in J.delta[p]:
                if q>=0 and q not in T and q not in seen:seen.add(q);todo.append(q)
    productive={f}
    while True:
        new=productive|{p for p,row in enumerate(J.delta) if any(q>=0 and q not in T and q in productive for q in row)}
        if new==productive:break
        productive=new
    expected={}
    def explore(t,p,word,seen):
        if p==f:expected[t,word]=None;return
        if p not in productive:return
        assert p not in seen, 'productive target-free cycle in claimed NO'
        for a,q in enumerate(J.delta[p]):
            if q>=0 and q not in T and q in productive:explore(t,q,word+(a,),seen|{p})
    for t in sorted(T):explore(t,t,(),set())
    proofs=answer['certificate']['prefix_exhaustions']
    assert len(proofs)==len(expected)
    assert {(p['target'],tuple(p['tail'])) for p in proofs}==set(expected)
    for proof in proofs:
        t=proof['target'];Y=tuple(proof['tail']);L=len(Y);assert L>0
        R={tuple(node) for node in proof['reachable']};assert (J.start,0) in R
        def move(q,a):
            s=Y[:q]+(a,)
            if len(s)>=L and s[-L:]==Y:return -1
            return max(r for r in range(L) if r<=len(s) and (r==0 or s[-r:]==Y[:r]))
        for p,q in R:
            assert 0<=p<J.k and 0<=q<L
            if p==t:
                r=q
                for a in Y[:-1]:
                    r=move(r,a)
                    if r<0:break
                assert r<0, 'successful prefix exit in NO certificate'
            for a,nxt in enumerate(J.delta[p]):
                r=move(q,a)
                if nxt>=0 and r>=0:assert (nxt,r) in R, 'prefix graph not closed'
    return len(proofs)


def sccs(I):
    closure=[]
    for p in range(I.k):
        seen={p};todo=[p]
        for q in todo:
            for r in I.delta[q]:
                if r>=0 and r not in seen:seen.add(r);todo.append(r)
        closure.append(seen)
    out=[];used=set()
    for p in range(I.k):
        if p in used:continue
        comp={q for q in closure[p] if p in closure[q]};used|=comp;out.append(comp)
    return out


def recurrent_properties(I):
    T={t for p,t in I.flags};S={p for p,t in I.flags}
    return any(len(c&T)>=2 and len(c&S)>=2 and
        any(sum(q in c for q in I.delta[p])>=2 for p in c) for c in sccs(I))


def test_main():
    rng=random.Random(SEED);counts=Counter();verdicts=Counter();fixtures={}
    for entries in product(range(-1,3),repeat=4):
        table=(entries[:2],entries[2:],(-1,-1))
        for mask in range(4):
            G=frozenset(pair for j,pair in enumerate(((0,1),(1,0))) if mask>>j&1)
            I=Instance(table,0,frozenset({2}),G);result=solve(I);verdicts[result['status']]+=1
            norm=normalize(I,2)
            if norm is not None:
                J,order=norm;cert=color_certificate(J)
                formula=compile_anchor(cert['instance']) if cert['status']=='CERTIFIED' else None
                for w in accepted_paths(J,8):
                    cword=encode(J,w,cert);a=witness(J,w)
                    assert a==reverse_witness(J,w)==witness(cert['colored_original'],cword)
                    if formula is not None:
                        assert a==witness(cert['instance'],cword)==anchored_word_test(cert['instance'],cword)==compiled_word_test(formula,cword)
                    counts['exhaustive_colored_word_comparisons']+=1
                if cert['status']=='CERTIFIED':
                    bound=0 if J.k==1 else J.k*J.k+J.k-2
                    expected=oracle_shortest(I,bound)
                    assert (result['status']=='YES')==(expected is not None)
                    if result['status']=='NO':
                        independent_column_no(cert['instance'],result['slices'][-1]);counts['negative_certificates_replayed']+=1
                    counts['complete_bound_oracles']+=1
            else:
                assert result['status']=='NO';counts['empty_slices']+=1
            if result['status']=='YES':assert witness(I,tuple(result['word']))
            counts['three_state_instances']+=1
    # Bad, every boundary flag type, arbitrary starts, empty words, multiple finals.
    for _ in range(320):
        k=rng.randrange(1,8);finals=frozenset(p for p in range(k) if rng.random()<.3)
        table=tuple(tuple(-1 if p in finals else rng.randrange(-1,k) for _ in range(2)) for p in range(k))
        G=frozenset((p,t) for p in range(k) for t in range(k) if rng.random()<.15)
        bad=frozenset(p for p in range(k) if rng.random()<.1)
        I=Instance(table,rng.randrange(k),finals,G,bad);ans=solve_with_tail_test(I)
        normalized=[normalize(I,f) for f in finals]
        for w in words(2,6):
            a=witness(I,w);assert a==reverse_witness(I,w)
            assert a==any(witness(n[0],w) for n in normalized if n is not None)
            counts['boundary_word_comparisons']+=1
        if ans['status']=='YES':assert witness(I,tuple(ans['word']))
        if ans['status']=='NO':
            for sl in ans['slices']:
                norm=normalize(I,sl['final'])
                if norm is not None:
                    J,_=norm;cert=color_certificate(J)
                    independent_column_no(cert['instance'],sl);counts['negative_certificates_replayed']+=1
        counts['boundary_instances']+=1
    # Complete target columns, including arbitrarily long target-free tail languages.
    for _ in range(450):
        k=rng.randrange(3,8);T={p for p in range(k-1) if rng.random()<.4}
        table=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k-1))+((-1,-1),)
        G=frozenset((p,t) for t in T for p in range(k-1) if p!=t)
        I=Instance(table,0,frozenset({k-1}),G);norm=normalize(I,k-1)
        if norm is None:continue
        J,_=norm;out=solve_columns(J)
        if out['status']=='NO':independent_column_no(J,out);counts['negative_certificates_replayed']+=1
        else:
            assert witness(J,out['word']) and reverse_witness(J,out['word']);counts['column_yes']+=1
            if out['infinite_tail']is not None:counts['infinite_tail_yes']+=1
        for w in accepted_paths(J,9):
            assert witness(J,w)==anchored_word_test(J,w);counts['dense_column_words']+=1
        counts['dense_column_instances']+=1
    # Every candidate in finite acyclic languages, independent of a small-model bound.
    for _ in range(150):
        k=rng.randrange(2,9)
        table=tuple(tuple(rng.choice([-1]+list(range(p+1,k))) for _ in range(2)) for p in range(k))
        G=frozenset((p,t) for p in range(k) for t in range(k) if rng.random()<.2)
        I=Instance(table,0,frozenset({k-1}),G);allw=list(accepted_paths(I,k))
        possible=any(witness(I,w) for w in allw);out=solve_with_tail_test(I)
        if out['status']!='UNKNOWN':assert (out['status']=='YES')==possible
        counts['complete_acyclic_languages']+=1;counts['acyclic_candidates']+=len(allw)
    for L in range(1,6):
        for Y in product(range(2),repeat=L):
            K=kmp_avoid(Y,2)
            for X in words(2,8):
                q=0
                for a in X:
                    q=K[q][a]
                    if q<0:break
                contained=any(X[i:i+L]==Y for i in range(len(X)-L+1))
                assert (q<0)==contained;counts['kmp_literal_comparisons']+=1
    # Direct periodic-prefix bound, including the exact k*d boundary.
    for _ in range(180):
        k=rng.randrange(2,7)
        table=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k-1))+((-1,-1),)
        I=Instance(table,0,frozenset({k-1}))
        for d in range(1,5):
            for B in product(range(2),repeat=d):
                q=I.start
                for n in range(1,k*d+1):
                    q=I.delta[q][B[(n-1)%d]]
                    if q<0:break
                    if q in I.finals:assert n<k*d;break
                counts['periodic_prefix_cases']+=1
    expected={'marking_barrier':'UNKNOWN','nonflat_target':'YES','exceptional_conjugacy':'YES',
              'recurrent_yes':'YES','recurrent_no':'NO','modular_positive_unknown':'UNKNOWN','sparse_cycle_yes':'YES'}
    for name,I in FIXTURES.items():
        J,order=normalize(I,next(iter(I.finals)));cert=color_certificate(J);out=solve_with_tail_test(I)
        assert out['status']==expected[name]
        for w in accepted_paths(J,12):
            cw=encode(J,w,cert)
            assert witness(J,w)==witness(cert['colored_original'],cw)
            if cert['status']=='CERTIFIED':assert witness(J,w)==anchored_word_test(cert['instance'],cw)
            counts['fixture_words']+=1
        if name.startswith('recurrent_'):
            assert recurrent_properties(J) and J.flags!=cert['instance'].flags
            assert cert['status']=='CERTIFIED'
        if out['status']=='NO':
            independent_column_no(cert['instance'],out['slices'][-1]);counts['negative_certificates_replayed']+=1
        fixtures[name]=dict(instance=I.as_json(),solution=out,certificate=certificate_json(cert),
                            recurrent_multi_source_target_nonflat=recurrent_properties(J))
    # Genuine positive input outside the certificate, not merely a known NO barrier.
    mod=FIXTURES['modular_positive_unknown'];mw=tuple(map(int,('1'*6+'0')*2))
    assert witness(mod,mw) and reverse_witness(mod,mw)
    cert=color_certificate(mod)
    assert cert['status']=='UNKNOWN' and not anchored_word_test(cert['instance'],encode(mod,mw,cert))
    fixtures['modular_positive_unknown']['known_witness']=mw
    cyc=FIXTURES['sparse_cycle_yes'];cert=color_certificate(cyc)
    assert cert['status']=='UNKNOWN'
    assert generic_unique_tail(cyc)['reason']=='productive target-free accepting tail'
    # Larger sparse graphs check the coloring independently of dense columns.
    for _ in range(600):
        k=rng.randrange(4,9)
        table=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k-1))+((-1,-1),)
        G=frozenset((p,t) for p in range(k-1) for t in range(k-1) if p!=t and rng.random()<.22)
        I=Instance(table,0,frozenset({k-1}),G);norm=normalize(I,k-1)
        if norm is None:continue
        J,_=norm;cert=color_certificate(J)
        formula=compile_anchor(cert['instance']) if cert['status']=='CERTIFIED' else None
        out=solve_with_tail_test(J)
        if out['status']=='YES':assert witness(J,out['word'])
        if out['status']=='NO':
            independent_column_no(cert['instance'],out['slices'][-1]);counts['negative_certificates_replayed']+=1
        for w in accepted_paths(J,9):
            cw=encode(J,w,cert);a=witness(J,w)
            assert a==reverse_witness(J,w)==witness(cert['colored_original'],cw)
            if formula is not None:
                assert a==anchored_word_test(cert['instance'],cw)==compiled_word_test(formula,cw)
            counts['sparse_coloring_words']+=1
        counts['sparse_certified' if formula is not None else 'sparse_uncertified']+=1
    proof=copy.deepcopy(fixtures['recurrent_no']['solution']['slices'][-1])
    proof['certificate']['prefix_exhaustions'][0]['reachable'].pop()
    try:independent_column_no(from_json(fixtures['recurrent_no']['certificate']['completed_instance']),proof)
    except AssertionError:counts['corrupted_no_certificates_rejected']+=1
    else:raise AssertionError('Broken negative certificate accepted')
    return dict(status='PASS',base_commit=BASE,seed=SEED,counts=dict(sorted(counts.items())),
                three_state_verdicts=dict(sorted(verdicts.items())),fixtures=fixtures,
                evidence_limits=['Finite tests do not replace the all-length proof.',
                'Small bounded NO oracles invoke the proved certified-class bound explicitly.',
                'Independent negative replay checks finite closure and exhaustive tail coverage.',
                'No Lean formalization or independent mathematical referee.',
                'UNKNOWN outside the sufficient class is not NO.'])


def compact(out):
    return {**{k:v for k,v in out.items() if k!='fixtures'},'fixtures':{
        name:dict(status=x['solution']['status'],word=x['solution'].get('word'),
                  states=len(x['instance']['delta']),colors=len(x['certificate']['classes']),
                  recurrent_multi_source_target_nonflat=x['recurrent_multi_source_target_nonflat'])
        for name,x in out['fixtures'].items()}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path);parser.add_argument('--full-output',type=Path)
    args=parser.parse_args()
    if not __debug__:parser.error('Run without -O; assertions must execute')
    out=test_main();small=compact(out)
    if args.output:args.output.write_text(json.dumps(small,indent=2,sort_keys=True)+'\n')
    if args.full_output:args.full_output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(small,indent=2,sort_keys=True))

if __name__=='__main__':main()

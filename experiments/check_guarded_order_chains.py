"""Independent word, weak-order, compiler and certificate checks.

No word-length cutoff is used for a NO oracle: the weak-order oracle is
complete on the stated symbolic class. Finite raw-word checks are diagnostics.
"""
from collections import Counter
from dataclasses import replace
from itertools import product
from math import gcd, lcm
from pathlib import Path
from random import Random
import hashlib
import json

from border_lab import Instance, witness, border_witness, words
from guarded_order_chains import (Chain, Domain, solve, verify, compile_chain,
                                  expand, check_values, clauses)
from search_calculus import weak_orders, stage_chain

ROOT=Path(__file__).resolve().parents[1]
SEED=2026090953


def effective_pairs(r):
    return [(2*i+a,2*j+b) for i in range(r) for j in range(i+1,r) for a in range(2) for b in range(2)]


def order_oracle(spec):
    # Independent, complete but exponentially slower: enumerate weak orders.
    # Every equality class must have compatible congruences. Compatible classes
    # have unbounded common domains and can be placed in ANY prescribed order.
    I=stage_chain(len(spec.domains),spec.flags)
    for pattern in weak_orders(len(spec.domains)):
        compatible=all(pattern[i]!=pattern[j] or
            (a.residue-b.residue)%gcd(a.modulus,b.modulus)==0
            for i,a in enumerate(spec.domains) for j,b in enumerate(spec.domains))
        if compatible and witness(I,expand(pattern)):
            return True
    return False


def check():
    rng=Random(SEED);counts=Counter();hist={}
    for r in range(1,4):
        pairs=effective_pairs(r);totals=Counter()
        for bits in range(1<<len(pairs)):
            flags=frozenset(p for j,p in enumerate(pairs) if bits>>j&1)
            spec=Chain((Domain(),)*r,flags)
            ans=solve(spec)
            assert (ans['status']=='YES')==order_oracle(spec)
            assert verify(spec,ans)
            if ans['status']=='YES':
                word=expand(ans['values']);I=stage_chain(r,flags)
                assert witness(I,word) and border_witness(I,word)
                assert len(word)<=r*(r+1)
                counts['checked_positive_words']+=1
            totals[ans['status']]+=1;counts['exhaustive_annotations']+=1
        hist[str(r)]=dict(totals)
    assert hist['3']=={'YES':709,'NO':3387}
    # All flags, including all boundary and ineffective roles, on one stage.
    r=1;pairs=list(product(range(3),repeat=2))
    for bits in range(1<<len(pairs)):
        flags=frozenset(p for j,p in enumerate(pairs) if bits>>j&1)
        spec=Chain((Domain(modulus=3,residue=2),),flags)
        ans=solve(spec)
        assert (ans['status']=='YES')==order_oracle(spec) and verify(spec,ans)
        counts['all_role_boundary_instances']+=1
    # Infinite modular languages, checked by complete weak-order oracles.
    for t in range(700):
        r=rng.randrange(1,6)
        ds=tuple(Domain(rng.randrange(1,8),0,rng.randrange(1,8)) for _ in range(r))
        ds=tuple(replace(d,residue=rng.randrange(d.modulus)) for d in ds)
        options=effective_pairs(r) if t%4 else list(product(range(2*r+1),repeat=2))
        flags=frozenset(p for p in options if rng.random()<.18)
        spec=Chain(ds,flags);ans=solve(spec)
        assert verify(spec,ans) and (ans['status']=='YES')==order_oracle(spec)
        counts['complete_modular_oracles']+=1;counts['modular_'+ans['status']]+=1
        if ans['status']=='YES' and ans['length']<1200:
            I,_=compile_chain(spec)
            w=expand(ans['values']);assert witness(I,w) and border_witness(I,w)
            counts['modular_positive_DFA_checks']+=1
        # Check the formula against concrete words without sharing its logic.
        if t<100:
            I,_=compile_chain(spec)
            for values in product(range(1,5),repeat=r):
                w=expand(values)
                assert check_values(spec,values)==witness(I,w)==border_witness(I,w)
                counts['literal_modular_count_vectors']+=1
    # The actual DFA candidate language, not merely its witness formula.
    for t in range(100):
        r=rng.randrange(1,4)
        ds=[]
        for _ in range(r):
            m=rng.randrange(1,5);ds.append(Domain(rng.randrange(1,4),rng.randrange(m),m))
        spec=Chain(tuple(ds));I,_=compile_chain(spec)
        for w in words('01',10):
            pieces=w.split('1')
            expected=(len(pieces)==r+1 and pieces[-1]=='' and all(
                set(u)<={'0'} and len(u)>=d.lower and len(u)%d.modulus==d.residue
                for u,d in zip(pieces,ds)))
            assert I.admissible(w)==expected
            counts['raw_compiler_words']+=1
    # Arbitrarily many stages: replay certificates, not an exhaustive census.
    large=[]
    for r in (8,16,32,64):
        equality=frozenset((a,b) for i in range(r-1) for a,b in [(2*i,2*r-1),(2*i+1,2*r-2)])
        ds=tuple(Domain(modulus=1+(i%7)) for i in range(r))
        spec=Chain(ds,equality);yes=solve(spec)
        P=lcm(*(d.modulus for d in ds))
        assert yes['status']=='YES' and yes['values']==[P]*r and verify(spec,yes)
        negative=replace(spec,flags=equality|{(0,2)})
        no=solve(negative);assert no['status']=='NO' and verify(negative,no)
        counts['unbounded_stage_family_queries']+=2
        large.append(dict(stages=r,period=P,positive_length=yes['length'],no_steps=len(no['steps'])))
    # Huge witnesses represented exactly in polynomially many bits.
    periods=(101,103,107,109,113,127,131,137,139,149,151,157)
    r=len(periods);equality=frozenset((a,b) for i in range(r-1) for a,b in [(2*i,2*r-1),(2*i+1,2*r-2)])
    huge=Chain(tuple(Domain(modulus=p) for p in periods),equality)
    huge_ans=solve(huge);P=lcm(*periods)
    assert huge_ans['values']==[P]*r and verify(huge,huge_ans)
    # Noncoprime contradictory and compatible equality domains.
    eq=frozenset({(0,3),(1,2)})
    impossible=Chain((Domain(modulus=4),Domain(residue=1,modulus=6)),eq)
    conflict=solve(impossible);assert conflict['status']=='NO' and verify(impossible,conflict)
    possible=Chain((Domain(residue=1,modulus=4),Domain(residue=3,modulus=6)),eq)
    good=solve(possible);assert good['values']==[9,9] and verify(possible,good)
    # A false generalization: flags may NOT be projected from one cycle phase
    # to an entire interior role. Equal-length even blocks have no such hit.
    phase_spec=Chain((Domain(modulus=2),Domain(modulus=2)))
    I,roles=compile_chain(phase_spec)
    odd0=next(i for i,r0 in enumerate(roles) if r0==1)
    even1=[i for i,r0 in enumerate(roles) if r0==3][1]
    J=replace(I,flags=frozenset({(odd0,even1)}))
    w='001001';assert witness(J,w) and border_witness(J,w)
    wrong=replace(phase_spec,flags=frozenset({(1,3)}));assert solve(wrong)['status']=='NO'
    # Explicit malformed and forged-proof checks.
    bad=Chain((Domain(),Domain()),eq|{(0,2)});proof=solve(bad)
    assert proof['status']=='NO' and verify(bad,proof)
    corrupted=dict(proof,steps=proof['steps'][:1]);assert not verify(bad,corrupted);counts['guards']+=1
    assert not verify(impossible,dict(conflict,steps=[]));counts['guards']+=1
    assert not verify(huge,dict(huge_ans,values=[1]*r));counts['guards']+=1
    assert not verify(bad,dict(proof,steps=[999]));counts['guards']+=1
    for f in (lambda:Domain(lower=0),lambda:Domain(modulus=0),lambda:Domain(residue=2,modulus=2),
              lambda:Chain((),frozenset()),lambda:compile_chain(huge,max_states=2),
              lambda:expand(huge_ans['values'],max_length=100)):
        try:f()
        except ValueError:counts['guards']+=1
        else:raise AssertionError('Expected rejection')
    sources={}
    for name in ('guarded_order_chains.py','check_guarded_order_chains.py','border_lab.py','search_calculus.py'):
        sources[name]=hashlib.sha256((ROOT/'experiments'/name).read_bytes()).hexdigest()
    out=dict(status='PASS',seed=SEED,counts=dict(counts),complete_small_census=hist,
             large_stage_cases=large,huge_equal_count=dict(periods=periods,count=P,answer=huge_ans),
             noncoprime_conflict=conflict,noncoprime_positive=good,
             phase_sensitive_limit=dict(delta=J.delta,flags=sorted(J.flags),witness=w),
             source_sha256=sources,
             scope='Complete for supplied modular phase-blind serial unary chains, not arbitrary terminal instances',
             proof_status='Written all-input class proof, independent-algorithm checks; mathematical review pending; not Lean-checked')
    (ROOT/'results'/'guarded-order-chains.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ('status','counts','complete_small_census','large_stage_cases','huge_equal_count')},indent=2))
    return out


if __name__=='__main__':check()

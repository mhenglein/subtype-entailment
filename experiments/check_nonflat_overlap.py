"""Reproduce the necessary-nonflat witness and bounded-overlap certificates.

Mathematical proofs are in notes/2026-09-05-nonflat-overlap.md. Exhaustive and
seeded checks are bounded evidence, not a proof of unrestricted decidability.
"""
from dataclasses import replace
from itertools import product
from pathlib import Path
import json
import random
import re
from border_lab import Instance, Sandwich, witness, border_witness, words, necessary, sufficient
from terminal_realization import realize
from denial_bridge import build, Canonical
from flat_terminal import flat_schemas
from terminal_overlap import overlap_certificate, bounded_overlap_decision

ROOT = Path(__file__).resolve().parents[1]
OBSTRUCTION = Instance(((1,-1),(2,3),(2,1),(4,-1),(-1,5),(-1,-1)),
                       frozenset({5}), frozenset({(0,3),(1,3)}))
NONREGULAR = Instance(((0,1),(2,-1),(2,3),(-1,-1)),
                     frozenset({3}), frozenset({(0,1)}))

def encode(I):
    return dict(delta=I.delta, final=sorted(I.final), flags=sorted(I.flags),
                bad=sorted(I.bad), start=I.start, alphabet=I.alphabet)


def all_subgraphs(I):
    edges = [(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row) if q>=0]
    for mask in range(1<<len(edges)):
        rows = [[-1,-1] for _ in I.delta]
        for i,(p,a) in enumerate(edges):
            if mask>>i&1:
                rows[p][a] = I.delta[p][a]
        yield replace(I,delta=tuple(map(tuple,rows)))


def fixture_checks():
    I = OBSTRUCTION
    counts = dict(words=0, canonical_models=0, all_edge_subgraphs=0,
                  flat_subgraphs=0, flat_nonempty_candidate_subgraphs=0,
                  exact_flat_NO=0, lower_budget_exhaustions=0)
    cert,_ = overlap_certificate(I,5)
    assert cert['status']=='BOUNDED' and cert['bound']==2
    answer = bounded_overlap_decision(I)
    assert answer['status']=='YES' and answer['word']=='0001101'
    R = realize(I)
    status, bridge = build(R.variables,R.constraints,R.alpha,R.beta)
    assert status=='SAT'
    for w in words('01',12):
        expected = re.fullmatch(r'0(?:0{2,}1)+101',w) is not None
        assert witness(I,w)==border_witness(I,w)==expected
        assert witness(bridge.instance,w)==expected
        assert necessary(I,w,2,0)==expected
        counts['words']+=1
        if len(w)<=8 or expected:
            actual = not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors()
            assert actual==expected
            counts['canonical_models']+=1
    for J in all_subgraphs(I):
        counts['all_edge_subgraphs']+=1
        cover=flat_schemas(J)
        if cover['status']=='COMPLETE':
            counts['flat_subgraphs']+=1
            counts['flat_nonempty_candidate_subgraphs']+=bool(cover['schemas'])
            out=bounded_overlap_decision(J)
            assert out['status']=='NO'
            assert Sandwich(J,2,0).search()['status']=='NO'
            counts['exact_flat_NO']+=1
    for B in range(2):
        for L in range(B+1):
            assert Sandwich(I,L,B-L,True).search()['status']=='NO'
            counts['lower_budget_exhaustions']+=1
    assert sufficient(I,'0001101',2,0)
    for pair, expected in (((0,3),'0101'),((1,3),'001101')):
        J=replace(I,flags=I.flags-{pair})
        assert witness(J,expected) and border_witness(J,expected)
    negative=replace(I,flags=I.flags|{(2,3)})
    assert bounded_overlap_decision(negative)['status']=='NO'
    assert flat_schemas(I)['status']=='UNKNOWN'
    assert flat_schemas(negative)['status']=='UNKNOWN'
    assert overlap_certificate(NONREGULAR,3)[0]['status']=='CYCLIC'
    assert bounded_overlap_decision(NONREGULAR)['status']=='UNKNOWN'
    # A productive product cycle through a flagged vertex is NOT an obstacle.
    cyclic_with_reset=replace(NONREGULAR,flags=NONREGULAR.flags|{(0,2)})
    reset_cert,_=overlap_certificate(cyclic_with_reset,3)
    assert reset_cert['status']=='BOUNDED' and reset_cert['bound']==1
    assert bounded_overlap_decision(cyclic_with_reset)['status']=='NO'
    assert bounded_overlap_decision(I,max_states=1)['status']=='UNKNOWN'
    assert bounded_overlap_decision(I,max_pair_vertices=1)['status']=='UNKNOWN'
    assert bounded_overlap_decision(Instance(((0,0),),frozenset({0})))['status']=='UNKNOWN'
    return dict(counts=counts,instance=encode(I),realization_variables=R.variables,
                exact_language='0 (0^{r} 1, r>=2)^+ 101',
                shortest_word='0001101',shortest_length=7,exact_budget=2,
                certificate=cert,negative_variant=encode(negative),
                flagged_cycle_fixture=encode(cyclic_with_reset),
                flagged_cycle_certificate=reset_cert)


def four_state_census():
    pairs=((0,1),(0,2),(1,2),(2,1))
    counts=dict(instances=0,YES=0,NO=0,UNKNOWN=0,cyclic_slices=0,
                maximum_overlap_bound=0,classified_nonflat=0,
                classified_nonflat_YES=0,classified_nonflat_NO=0)
    oracle_words=list(words('01',4))
    for row in product((-1,1,2,3),repeat=6):
        delta=tuple(tuple(row[2*p:2*p+2]) for p in range(3))+((-1,-1),)
        for mask in range(16):
            I=Instance(delta,frozenset({3}),frozenset(p for i,p in enumerate(pairs) if mask>>i&1))
            out=bounded_overlap_decision(I)
            counts['instances']+=1
            counts[out['status']]+=1
            oracle=any(witness(I,w) for w in oracle_words)
            if out['status']!='UNKNOWN':
                assert (out['status']=='YES')==oracle
                if flat_schemas(I)['status']=='UNKNOWN':
                    counts['classified_nonflat']+=1
                    counts['classified_nonflat_'+out['status']]+=1
            for d in out['slices']:
                c=d['certificate']
                counts['cyclic_slices']+=c['status']=='CYCLIC'
                counts['maximum_overlap_bound']=max(counts['maximum_overlap_bound'],c.get('bound',0))
    return counts


def random_checks():
    rng=random.Random(2026090537)
    counts=dict(instances=0,YES=0,NO=0,UNKNOWN=0,predicate_comparisons=0,
                checked_nonmerging_agreements=0,certificate_slices=0,
                cyclic_slices=0,maximum_overlap_bound=0)
    examples=[]
    for attempt in range(600):
        k=rng.randrange(2,9)
        finals=frozenset(p for p in range(k) if rng.random()<.25)
        delta=tuple((-1,-1) if p in finals else tuple(rng.randrange(-1,k) for _ in range(2))
                    for p in range(k))
        flags=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.13)
        bad=frozenset(p for p in range(k) if rng.random()<.04)
        I=Instance(delta,finals,flags,bad,rng.randrange(k))
        out=bounded_overlap_decision(I)
        counts['instances']+=1;counts[out['status']]+=1
        for f in finals:
            cert,J=overlap_certificate(I,f)
            if cert['status']=='CYCLIC':counts['cyclic_slices']+=1
            if cert['status']!='BOUNDED':continue
            L=cert['bound'];counts['certificate_slices']+=1
            counts['maximum_overlap_bound']=max(counts['maximum_overlap_bound'],L)
            for w in words('01',7):
                counts['predicate_comparisons']+=1
                assert witness(J,w)==border_witness(J,w)==necessary(J,w,L,0)
                c=J.run(w)
                if c is None or not J.admissible(w):continue
                n=len(w)
                height=[1]*(n+1)
                for i in range(n-1,-1,-1):
                    height[i]=1+max((height[j] for j in range(i+1,n+1)
                                     if w[i:].startswith(w[j:])),default=0)
                assert max(height)<=len(I.delta)
                lengths=[n-j for i in range(n) for j in range(i+1,n)
                         if (c[i],c[j]) in J.flags and w[i:].startswith(w[j:])]
                if lengths: assert min(lengths)<=L
                for i in range(n):
                    for j in range(i+1,n):
                        if not w[i:].startswith(w[j:]):continue
                        assert all(c[i+t]!=c[j+t] for t in range(n-j+1))
                        counts['checked_nonmerging_agreements']+=1

            if len(examples)<3 and L>0 and flat_schemas(J)['status']=='UNKNOWN':
                examples.append(dict(instance=encode(I),certificate=cert,decision=out['status']))
    return dict(counts=counts,seed=2026090537,nonflat_examples=examples)


def main():
    fixture=fixture_checks()
    print('Nonflat obstruction and canonical models PASS',flush=True)
    census=four_state_census()
    print('Four-state overlap census PASS',census,flush=True)
    random=random_checks()
    print('Random overlap identities PASS',random['counts'],flush=True)
    out=dict(status='PASS',fixture=fixture,four_state_census=census,random=random,
             scope='Exact under a written acyclic last-flag synchronized-pair certificate; cyclic cases remain UNKNOWN',
             proof_status='Written proofs plus reproducible checks, not Lean-checked',
             no_general_bound_claim=True)
    (ROOT/'results/nonflat-overlap.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Saved results/nonflat-overlap.json',flush=True)

if __name__=='__main__':main()

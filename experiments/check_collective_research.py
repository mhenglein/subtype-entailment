"""Reproduce collective, exact-gap, and cross-gap research checks.

All finite counts describe exactly the loops below. All-length claims are
proved separately. Nothing here labels a capped or merely short search NO.
"""
from dataclasses import replace
from itertools import product
from pathlib import Path
from random import Random
import hashlib,json

from border_lab import Instance, Sandwich, witness,border_witness,words,necessary
from collective_transport import (backward_closure,verify_rewrite,rewrite,
                                 barrier,transported_barrier,gap_set)
from gap_equivalence import (implication,orbit_implication,equivalent,saturate,
                             Limits,bad_gaps,equality_cycle)
from power_transport import harmonic_implication,saturate as power_saturate,periodic_grid
from lastflag_spectrum import spectrum,decide,is_lastflag
from search_calculus import test as stage_test,stage_chain,weak_orders,profile_flags
from calculus_limits import short_detectable_limit

ROOT=Path(__file__).resolve().parents[1]
SEED=2026090874


def profile(I,w):
    c=I.run(w);n=len(w)
    if c is None or not I.admissible(w):return None
    return {d:{(c[i],c[i+d]) for i in range(n-d+1)
               if w[i:].startswith(w[i+d:])} for d in range(n+1)}


def finite_language(I):
    # Called only on strictly increasing-index acyclic tables.
    todo=[(I.start,'')];out=[]
    while todo:
        p,w=todo.pop()
        if p in I.bad:continue
        if p in I.final:out.append(w)
        for a,q in enumerate(I.delta[p]):
            if q>=0:
                assert q>p
                todo.append((q,w+str(a)))
    return out


def check_counterexample(I,G,H,result):
    if result['status']=='COUNTEREXAMPLE':
        w=result['word'];d=result['gap'];p=profile(I,w)
        assert p is not None and p[d]&set(G) and not p[d]&set(H)
        return 1
    return 0


def small_tables(counts):
    # Fixed terminal last state, arbitrary nonfinal transition rows, every
    # off-diagonal nonfinal G,H. This is 4,106 implication queries in total.
    for k in range(1,4):
        possible=[(p,q) for p in range(k-1) for q in range(k-1) if p!=q]
        flagsets=[frozenset(p for j,p in enumerate(possible) if mask>>j&1)
                  for mask in range(1<<len(possible))]
        for rows in product(product(range(-1,k),repeat=2),repeat=k-1):
            I=Instance(tuple(rows)+((-1,-1),),frozenset({k-1}))
            counts['terminal_tables']+=1
            oracle=[p for w in words('01',7) if (p:=profile(I,w)) is not None]
            counts['raw_small_words']+=255
            for G in flagsets:
                original=replace(I,flags=G)
                closure,rules=backward_closure(original)
                assert verify_rewrite(original,closure)
                lifted=rewrite(original,closure)
                counts['backward_closures']+=1
                for p in oracle:
                    assert {d for d,x in p.items() if x&G}=={d for d,x in p.items() if x&closure}
                    counts['closure_word_checks']+=1
                for H in flagsets:
                    one=implication(I,G,H,Limits(actions=None,checks=None))
                    two=orbit_implication(I,G,H,None)
                    assert one['status']==two['status'] and one['status']!='UNKNOWN'
                    counts['small_backend_queries']+=1
                    counts['reconstructed_counterexamples']+=check_counterexample(I,G,H,one)
                    counts['reconstructed_counterexamples']+=check_counterexample(I,G,H,two)
                    if one['status']=='IMPLIES':
                        assert not any(x&G and not x&H for p in oracle for x in p.values())
                    counts['small_bounded_implication_checks']+=len(oracle)


def acyclic_oracles(rng,counts):
    for case in range(240):
        k=rng.randrange(1,8)
        rows=tuple(tuple(rng.choice([-1]+list(range(p+1,k))) for a in range(2)) for p in range(k))
        finals=frozenset(p for p,row in enumerate(rows) if row==(-1,-1) and rng.random()<.85)
        I=Instance(rows,finals,bad=frozenset(p for p in range(k) if rng.random()<.05),start=rng.randrange(k) if case%5==0 else 0)
        language=finite_language(I);oracles=[profile(I,w) for w in language]
        counts['acyclic_instances']+=1;counts['complete_candidate_words']+=len(language)
        for query in range(4):
            G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.2)
            H=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.2)
            expected=not any(x&G and not x&H for o in oracles for x in o.values())
            a=implication(I,G,H,Limits(None,None));b=orbit_implication(I,G,H,None)
            assert a['status']==b['status']==('IMPLIES' if expected else 'COUNTEREXAMPLE')
            counts['complete_implication_oracles']+=1
            counts['reconstructed_counterexamples']+=check_counterexample(I,G,H,a)+check_counterexample(I,G,H,b)
        G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.13)
        A=(rng.randrange(k),rng.randrange(k))
        if A[0]!=A[1]:
            has_failure=False
            for w in language:
                c=I.run(w)
                for i in range(len(w)+1):
                    for j in range(i+1,len(w)+1):
                        if (c[i],c[j])==A and w[i:].startswith(w[j:]):
                            grid=periodic_grid(I,w,i,j-i)
                            if not any((r,s) in G for x,y,r,s in grid):has_failure=True
            a=harmonic_implication(I,A,G,None)
            assert a['status']==('NOT_CERTIFIED' if has_failure else 'CERTIFIED')
            counts['complete_grid_oracles']+=1
        original=replace(I,flags=G)
        record,J=power_saturate(original,None)
        assert record['status']=='SATURATED_IN_CALCULUS'
        for w in language:
            assert witness(original,w)==witness(J,w)==border_witness(J,w)
            counts['complete_power_word_checks']+=1
        counts['complete_power_normalizations']+=1


def cyclic_queries(rng,counts):
    for case in range(220):
        k=rng.randrange(2,6)
        rows=tuple(tuple(-1 if rng.random()<.16 else rng.randrange(k) for a in range(2)) for p in range(k-1))+((-1,-1),)
        G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<(.04 if case%2 else .16))
        H=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<(.12 if case%3 else .3))
        I=Instance(rows,frozenset({k-1}),G,bad=frozenset(p for p in range(k) if rng.random()<.03))
        a=implication(I,G,H);b=orbit_implication(I,G,H,200000)
        if 'UNKNOWN' not in (a['status'],b['status']):assert a['status']==b['status']
        else:counts['capped_backend_queries']+=1
        counts['cyclic_backend_queries']+=1
        counts['reconstructed_counterexamples']+=check_counterexample(I,G,H,a)+check_counterexample(I,G,H,b)
        rec,J=power_saturate(I,50000)
        counts['cyclic_power_normalizations']+=1
        if rec['status']=='PARTIAL':counts['capped_normalizations']+=1
        for w in words('01',7):
            assert witness(I,w)==witness(J,w)==border_witness(J,w)
            counts['cyclic_power_raw_words']+=1


def analytic(counts):
    I=barrier();J=transported_barrier()
    incoming=[[] for _ in I.delta]
    for p,row in enumerate(I.delta):
        for a,q in enumerate(row):
            if q>=0:incoming[q].append((p,a))
    old_transports=[]
    for p in range(len(I.delta)):
        for q in range(len(I.delta)):
            if p==q or p in I.final or q in I.final:continue
            common=[a for a in range(2) if min(I.delta[p][a],I.delta[q][a])>=0]
            if len(common)!=1:continue
            a=common[0];r,s=I.delta[p][a],I.delta[q][a]
            if r!=s and I.start not in (r,s) and incoming[r]==[(p,a)] and incoming[s]==[(q,a)]:
                old_transports.append(((p,q),(r,s)))
    assert not old_transports, 'The fixture must not be a one-edge transport case'
    assert equivalent(I,I.flags,J.flags,Limits(None,None))['status']=='EQUIVALENT_GAPS'
    saturated,K=saturate(I,Limits(None,None))
    assert saturated['status']=='MAXIMAL_GAP_EQUIVALENT'
    bound=spectrum(K);decision=decide(K)
    assert bound['H']==2 and decision['status']=='NO'
    counts['analytic_equivalence_words']=0
    for w in words('01',13):
        assert witness(I,w)==witness(J,w)==witness(K,w)==border_witness(K,w)
        assert gap_set(I,w)==gap_set(J,w)==gap_set(K,w)
        counts['analytic_equivalence_words']+=1
    for m in range(1,65):
        w='0'*(2*m)+'1'+'0'*m+'10'
        orig=[(i,j) for i in range(len(w)+1) for j in range(i+1,len(w)+1)
              if (I.run(w)[i],I.run(w)[j]) in I.flags and w[i:].startswith(w[j:])]
        assert orig==[(m,2*m+1)]
        assert witness(I,w)==witness(J,w)==False
        assert necessary(J,w,2,0)==False
        counts['barrier_family_checks']+=1
    # The cross-gap contradiction. Exact saturation adds only impossible pairs.
    E=equality_cycle();er,ES=saturate(E,Limits(None,None))
    assert er['status']=='MAXIMAL_GAP_EQUIVALENT'
    for query in er['checks']:
        independent=orbit_implication(E,{tuple(query['pair'])},E.flags,None)
        assert independent['status']==query['status']
        counts['seven_state_maximality_backend_agreements']+=1
    for pair in ES.flags-E.flags:
        z=implication(E,{pair},set(),Limits(None,None))
        assert z['status']=='IMPLIES'
        assert orbit_implication(E,{pair},set(),None)['status']=='IMPLIES'
        counts['vacuous_added_pair_proofs']+=1
    assert spectrum(ES)['status']=='UNBOUNDED'
    cross=harmonic_implication(E,(0,2),max_states=None)
    assert cross['status']=='CERTIFIED'
    assert equivalent(E,E.flags,E.flags|{(0,2)},Limits(None,None))['status']=='DIFFERENT_GAPS'
    pr,P=power_saturate(E,None)
    assert (4,6) in P.flags and decide(P)['status']=='NO'
    for n,m,l in product(range(1,7),repeat=3):
        w='0'*n+'1'+'0'*m+'1'+'0'*l+'1'
        assert not witness(E,w) and not witness(P,w)
        counts['equality_cycle_vectors']+=1
    for n in range(1,65):
        w=('0'*n+'1')*3
        assert bad_gaps(E,w)==bad_gaps(ES,w)=={2*(n+1)}
        c=E.run(w)
        badpairs=[(i,j) for i in range(len(w)+1) for j in range(i+1,len(w)+1)
                  if (c[i],c[j]) in ES.flags and w[i:].startswith(w[j:])]
        assert badpairs==[(0,2*(n+1))]
        assert necessary(ES,w,n,n)
        counts['equality_cycle_escaping_family']+=1
    return dict(six_state_barrier=dict(delta=I.delta,original=sorted(I.flags),rewritten=sorted(J.flags),
                                     saturation=saturated,analysis=bound,decision=decision),
                seven_state_cross_gap=dict(delta=E.delta,original=sorted(E.flags),gap_saturation=er,
                    gap_spectrum=spectrum(ES),cross_gap_certificate=cross,power_saturation=pr,decision=decide(P)))


def calculus_limit(counts):
    I,names=short_detectable_limit()
    rec,J=power_saturate(I,None)
    assert rec['status']=='SATURATED_IN_CALCULUS'
    assert backward_closure(J)[0]==J.flags
    # Certify the finite fixed point directly, including unsuccessful rules.
    checks=[]
    for p in range(len(I.delta)):
        for q in range(len(I.delta)):
            if p==q or p in I.final or (p,q) in J.flags:continue
            ans=harmonic_implication(J,(p,q),max_states=None)
            assert ans['status']=='NOT_CERTIFIED'
            assert not any((a,b) in J.flags for i,j,a,b in periodic_grid(J,ans['word'],ans['i'],ans['gap']))
            counts['calculus_limit_failed_rules']+=1
            checks.append(dict(pair=[p,q],result=ans))
    analysis=spectrum(J); no=Sandwich(I,1,0).search()
    assert analysis['status']=='UNBOUNDED' and no['status']=='NO'
    for w in words('01',14):
        counts['calculus_limit_raw_words']+=1
        if I.admissible(w):
            assert not witness(I,w) and not witness(J,w) and not border_witness(J,w)
            assert not necessary(I,w,1,0)
            counts['calculus_limit_accepted_words']+=1
    for r in range(33):
        z='10'+'1'*(3*r+2)+'0';w='0'+z+z
        assert is_lastflag(J,w,1,1+len(z))
        assert len(w)-(1+len(z))==3*r+5
        counts['calculus_limit_unbounded_family']+=1
    return dict(delta=I.delta,original_flags=sorted(I.flags),state_names=names,
                saturation=rec,remaining_grid_rule_counterexamples=checks,
                spectrum=analysis,separate_short_NO=no,
                limitation='The finite calculus followed ONLY by bounded last-aligned length is incomplete; Necessary(1,0) independently solves this fixture.')


def guards(counts):
    # Same gap before the proposed periodic tail: the last-letter guard is essential.
    I=Instance(((1,-1),(2,-1),(3,-1),(-1,-1)),frozenset({3}))
    G={(1,2)};H={(0,1)}
    assert bad_gaps(I,'000',G)==bad_gaps(I,'000',H)=={1}
    assert implication(I,G,H,Limits(None,None))['status']=='IMPLIES'
    counts['guard_regressions']+=1
    # Dropping the source-start exclusion incorrectly adds (0,2).
    I=Instance(((0,1),(2,1),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert (0,2) not in backward_closure(I)[0]
    assert witness(I,'10') and not witness(replace(I,flags=I.flags|{(0,2)}),'10')
    counts['guard_regressions']+=1
    # Equal-letter reversal, not arbitrary paired predecessors.
    I=Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert (1,2) not in backward_closure(I)[0] and witness(I,'01')
    counts['guard_regressions']+=1
    I=Instance(((-1,-1),),frozenset({0}))
    r=implication(I,{(0,0)},set());assert (r['word'],r['gap'])==('',0)
    counts['guard_regressions']+=1
    I=Instance(((1,-1),(-1,-1)),frozenset({1}))
    r=implication(I,{(0,1)},set());assert (r['word'],r['gap'])==('0',1)
    counts['guard_regressions']+=1
    I=barrier()
    assert implication(I,{(1,3)},I.flags,Limits(actions=1,checks=None))['status']=='UNKNOWN'
    assert implication(I,{(1,3)},I.flags,Limits(actions=None,checks=1))['status']=='UNKNOWN'
    assert orbit_implication(I,{(1,3)},I.flags,1)['status']=='UNKNOWN'
    assert harmonic_implication(equality_cycle(),(0,2),max_states=1)['status']=='UNKNOWN'
    counts['guard_regressions']+=4
    for make in [lambda:Limits(actions=0),lambda:Limits(checks=True),
                 lambda:implication(Instance(((0,0),),frozenset({0})),set(),set()),
                 lambda:implication(I,{(99,0)},set())]:
        try:make()
        except ValueError:counts['guard_regressions']+=1
        else:raise AssertionError('Invalid input was accepted')


def run():
    from collections import defaultdict
    counts=defaultdict(int);rng=Random(SEED)
    small_tables(counts);acyclic_oracles(rng,counts);cyclic_queries(rng,counts)
    fixtures=analytic(counts);fixtures['calculus_limit']=calculus_limit(counts);guards(counts)
    stage3=stage_test(3)
    assert stage3['yes']==709 and stage3['no']==stage3['closed']==3387 and not stage3['misses']
    stage3.pop('seconds')
    # Verify the finite-order stage oracle against a genuinely different direct
    # word implementation on every ordered partition and every effective flag.
    for r in range(1,5):
        pairs=[(2*i+a,2*j+b) for i in range(r) for j in range(i+1,r) for a in range(2) for b in range(2)]
        for vector in weak_orders(r):
            formula=profile_flags(vector,pairs);w=''.join('0'*n+'1' for n in vector)
            for bit,pair in enumerate(pairs):
                I=stage_chain(r,{pair})
                assert bool(formula>>bit&1)==(not witness(I,w))
                counts['stage_oracle_direct_checks']+=1
    sources={}
    for name in ['collective_transport.py','gap_equivalence.py','power_transport.py','search_calculus.py',
                 'calculus_limits.py','check_collective_research.py','border_lab.py','lastflag_spectrum.py']:
        data=(ROOT/'experiments'/name).read_bytes()
        sources[name]=hashlib.sha256(data).hexdigest()
    out=dict(status='PASS',seed=SEED,proof_status='Written proof; independent review pending; not Lean-checked',
             scope='Exact gap-relation decisions and sound cyclic/cross-gap normalization; not unrestricted Problem 1.7',
             counts=dict(sorted(counts.items())),three_stage_complete_census=stage3,fixtures=fixtures,source_sha256=sources)
    path=ROOT/'results'/'collective-gap-research.json';path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=out['status'],counts=out['counts'],stage3=stage3),indent=2))

if __name__=='__main__':run()

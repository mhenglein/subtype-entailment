#!/usr/bin/env python3
"""Deterministic bounded checks; never an unrestricted emptiness decision."""
from __future__ import annotations
import argparse, itertools, json, random
from collections import Counter
from closed_walk_lift import *

SEED=2026091217

def words(n):
    for length in range(n+1):
        for bits in itertools.product('01',repeat=length):yield ''.join(bits)

def all_paths(I,p,max_length):
    out=[];todo=[('',[p])]
    while todo:
        w,c=todo.pop()
        if c[0] in I.bad:continue
        out.append((w,c))
        if len(w)==max_length:continue
        for a in (0,1):
            q=I.delta[c[-1]][a]
            if q>=0 and q not in I.bad:todo.append((w+str(a),c+[q]))
    return out

def random_instance(rng,k):
    finals={k-1}
    if k>=4 and rng.random()<.15:finals.add(k-2)
    tab=tuple((-1,-1) if q in finals else tuple(rng.randrange(-1,k) for _ in range(2))
              for q in range(k))
    flags=frozenset((p,t) for p in range(k) for t in range(k) if rng.random()<.17)
    bad=frozenset(q for q in range(k) if rng.random()<.07)
    return Instance(tab,rng.randrange(k),frozenset(finals),bad,flags)

def check():
    rng=random.Random(SEED);stats=Counter();bounds={}
    # Semantic projection of the WHOLE flag relation, not merely selected cuts.
    for z in range(90):
        I=random_instance(rng,rng.randrange(2,7));d=1+z%4;J=counter_lift(I,d)
        stats['projection_instances']+=1
        for w in words(7):
            c,j=I.trace(w),J.trace(w)
            assert (c is None)==(j is None)
            if c is not None:
                r=0
                for idx,(q,qj) in enumerate(zip(c,j)):
                    if idx:r=(r+int(q in I.sources))%d
                    assert qj==q*d+r
                if c[-1] in I.finals:
                    v=w[::-1];rev=c[::-1]
                    for b in range(len(v)+1):
                        marks=[ell for ell in range(b+1) if v[:ell]==v[b-ell:b]]
                        assert len({rev[ell] for ell in marks})==len(marks)
                        assert len(marks)<=I.k
                    stats['terminal_border_width_words']+=1
            a=witness_direct(I,w);b=witness_reversed(I,w)
            assert a==b==witness_direct(J,w)==witness_reversed(J,w)
            stats['projection_words']+=1
    bounds['projection']={'instances':90,'states':'2..6','moduli':'1..4','all_binary_words_through':7}

    # Additive-count power lemma, without a first-return assumption on B.
    retained=[]
    for z in range(200):
        I=random_instance(rng,rng.randrange(2,6))
        for p in sorted(I.sources-I.bad-I.finals):
            paths=all_paths(I,p,6)
            loops=[(w,c) for w,c in paths if c[-1]==p]
            if not loops:continue
            bases=[(w,c) for w,c in loops if w]
            if len(bases)>18:bases=rng.sample(bases,18)
            for B,cb in bases:
                d=source_arrivals(I,B,p);J=counter_lift(I,d)
                offsets=[i for i,q in enumerate(cb[:-1]) if q in I.sources]
                assert len(offsets)==d and offsets[0]==0
                for a in offsets:
                    q=cb[a];R=B[a:]+B[:a]
                    assert first_return_dfa(J,q*d).accepts(R)
                    stats['rotated_first_returns']+=1
                for U,cu in loops:
                    expected=literal_power(B,U)
                    assert guarded_power(I,p,B,U)==expected
                    assert (U+B==B+U and path_dfa(J,p*d,{p*d}).accepts(U))==expected
                    stats['power_guard_pairs']+=1
                    if U+B==B+U and not expected:stats['fractional_commuters_rejected']+=1
                tails=[(w,c) for w,c in paths if c[-1] in I.finals and len(w)<=5]
                if tails and d<=4 and len(retained)<110:
                    Y,_=rng.choice(tails);retained.append((I,p,B,Y))
    bounds['power_guards']={'generated_tables':200,'loop_length_at_most':6,
                            'bases_per_pivot_at_most':18,'all_U_loops_through':6}

    # C071 algebra for every lifted occurrence of a nonsimple base, compared
    # with actual original-word cuts. Tail sources are deliberately NOT assumed
    # absent: the comparison is scoped to phase positions plus the exit pivot.
    for I,p,B,Y in retained:
        cb=I.trace(B,p);offsets=[i for i,q in enumerate(cb[:-1]) if q in I.sources]
        d=len(offsets);J=counter_lift(I,d)
        for m in range(5):
            W=B*m+Y
            positions=[b*len(B)+a for b in range(m) for a in offsets]+[m*len(B)]
            expected=boundary_good_direct(I,p,W,positions)
            actual=all(phi_value(I,p,t,Y) for q,t in I.flags if q==p)
            if m:
                for a in offsets:
                    q=cb[a];R=B[a:]+B[:a];Z=B[a:]+Y
                    got=repeated_boundary_value(J,q*d,R,m-1,Z)
                    direct=boundary_good_direct(J,q*d,R*(m-1)+Z,
                                                [j*len(R) for j in range(m)])
                    assert got==direct
                    actual=actual and got
                    stats['lifted_boundary_queries']+=1
            assert actual==expected
            stats['complete_phase_queries']+=1
    bounds['phase_rotation']={'retained_contexts':len(retained),'source_arrivals_per_base_at_most':4,
                              'copy_exponents':'0..4'}

    # Independently evaluate explicit equations and DFA atoms against a
    # constructed concrete assignment. This is not existential solver output.
    small=list(words(3))
    for V in small:
        for W in small:
            f=FormulaBuilder({'V':V,'W':W});v=f.named('V');w=f.named('W')
            bundle=f.finish(f.ns(v,w),{'solver_executed':False})
            assert evaluate_formula(bundle)==(not W.endswith(V))
            stats['nonsuffix_grounded_models']+=1

    # Boundary formula on arbitrary small terminal instances, including empty
    # captures, diagonal/final-column flags, and nontrivial conjugacies.
    count=0
    for z in range(500):
        if count>=100:break
        I=random_instance(rng,3)
        for p in range(I.k):
            if p in I.bad:continue
            paths=all_paths(I,p,5)
            bases=[w for w,c in paths if w and c[-1]==p and p not in c[1:-1]]
            tails=[w for w,c in paths if c[-1] in I.finals]
            if not bases or not tails:continue
            B=rng.choice(bases);Y=rng.choice(tails);m=count%4
            f=FormulaBuilder({'B':B,'U':B*m,'Y':Y})
            b,u,y=f.named('B'),f.named('U'),f.named('Y')
            bundle=f.finish(f.boundaries(I,p,b,u,y),{'solver_executed':False})
            expected=boundary_good_direct(I,p,B*m+Y,[j*len(B) for j in range(m+1)])
            got=evaluate_formula(bundle)
            assert got==expected==repeated_boundary_value(I,p,B,m,Y)
            stats['boundary_formula_grounded_models']+=1
            stats['boundary_formula_true_models' if got else 'boundary_formula_false_assignments']+=1
            count+=1
            if count>=100:break

    # Full one-phase scheme: the base is two first-return words chosen
    # independently; it is not a first-return word at the original source.
    I=example();phase=(Phase(0,(0,0)),)
    for a,b in itertools.product(('0','10'),repeat=2):
        for m in range(5):
            B=a+b;model={'C0':'','C1':'110','U0':B*m,'A0_0':a,'A0_1':b}
            bundle=compile_scheme(I,phase,model)
            expected=witness_direct(I,B*m+'110')
            assert evaluate_formula(bundle)==expected==witness_reversed(I,B*m+'110')
            stats['full_scheme_grounded_models']+=1
            stats['full_scheme_true_models' if expected else 'full_scheme_false_assignments']+=1
    # Two phase-local lifts; source 0 occurs twice in each prescribed base.
    # A final plain source-1 phase makes every source position explicit.
    for extra in ((1,0),(1,2),(1,1)):
        K=Instance(I.delta,0,I.finals,I.bad,I.flags|{extra})
        for m in range(3):
            ground={'C0':'','C1':'1','C2':'10','U0':'1010'*m,'U1':'',
                    'A0_0':'1','A0_1':'0','A0_2':'1','A0_3':'0'}
            bundle=compile_scheme(K,(Phase(0,(0,1,0,1)),Phase(1)),ground)
            expected=witness_direct(K,'1010'*m+'110')
            assert evaluate_formula(bundle)==expected
            stats['multisource_full_scheme_grounded_models']+=1
    # Two independently powered phases with different local moduli. Their
    # bases deliberately share a primary segment value; tails remain common.
    for m,n in itertools.product(range(3),repeat=2):
        ground={'C0':'','C1':'10','C2':'110','U0':'1010'*m,'U1':'101010'*n,
                'A0_0':'10','A0_1':'10','A1_0':'10','A1_1':'10','A1_2':'10'}
        bundle=compile_scheme(I,(Phase(0,(0,0)),Phase(0,(0,0,0))),ground)
        word='1010'*m+'10'+'101010'*n+'110'
        assert evaluate_formula(bundle)==witness_direct(I,word)
        assert bundle['metadata']['local_lift_state_counts']==[8,12]
        stats['different_modulus_shared_tail_models']+=1

    # Empty-star guards must not require any possible nonempty base.
    E=Instance(((1,-1),(-1,-1),(-1,-1)),0,frozenset({1}),frozenset(),frozenset({(0,2)}))
    bundle=compile_scheme(E,(Phase(0,(0,)),),{'C0':'','C1':'0','U0':''})
    assert evaluate_formula(bundle) and witness_direct(E,'0')
    assert all(not first_return_dfa(E,0).accepts(w) for w in words(6))
    # This particular graph has no directed cycle at all, so its base language
    # is provably empty, not merely absent from the bounded enumeration.
    assert E.delta[1]==E.delta[2]==(-1,-1) and E.delta[0]==(1,-1)
    stats['empty_star_without_base_models']+=1
    E=Instance(((-1,-1),(-1,-1)),0,frozenset({0}),frozenset(),frozenset({(0,1)}))
    bundle=compile_scheme(E,(Phase(0,(0,)),),{'C0':'','C1':'','U0':''})
    assert evaluate_formula(bundle) and witness_direct(E,'')
    stats['empty_star_without_base_models']+=1

    B,U='1010','10'
    assert U+B==B+U and I.trace(B)[-1]==I.trace(U)[-1]==0
    assert source_arrivals(I,B,0)==2 and source_arrivals(I,U,0)==1
    assert not guarded_power(I,0,B,U)
    assert witness_direct(I,B+'110') and not witness_direct(I,'0110')
    alias={'base':B,'fractional_commuter':U,'base_source_arrivals':2,
           'commuter_source_arrivals':1,'commutes':True,'whole_base_power':False,
           'counter_guard_accepts':False,'positive_word':B+'110','live_flag_word':'0110'}

    # A newly found one-flag interior-deletion obstruction. No minimality claim
    # across automata; the search that found it is saved separately.
    D=Instance(((0,1),(3,-1),(0,4),(2,0),(-1,-1)),1,frozenset({4}),frozenset(),frozenset({(1,0)}))
    w='01001011001';a,b=5,8;v=w[:a]+w[b:]
    assert witness_direct(D,w) and witness_reversed(D,w)
    assert D.trace(w)[a]==D.trace(w)[b]==1
    assert D.trace(v)[-1]==4 and not witness_direct(D,v) and not witness_reversed(D,v)
    assert v[0:].startswith(v[3:]) and (D.trace(v)[0],D.trace(v)[3])==(1,0)
    deletion={'instance':D.as_json(),'witness':w,'run':D.trace(w),'deleted_interval':[a,b],
              'deleted_word':w[a:b],'shortened':v,'shortened_run':D.trace(v),
              'new_forbidden_cuts':[0,3],'new_repeated_suffix':v[3:]}

    # Existing C071 exceptional-conjugacy regression, attributed rather than
    # reported as a new example.
    C=Instance(((1,3),(-1,2),(0,-1),(4,-1),(-1,5),(-1,-1)),0,
               frozenset({5}),frozenset(),frozenset({(0,2)}))
    f=FormulaBuilder({'B':'010','U':'010010','Y':'101'});bb,uu,yy=f.named('B'),f.named('U'),f.named('Y')
    bundle=f.finish(f.boundaries(C,0,bb,uu,yy),{'solver_executed':False})
    assert phi_value(C,0,2,'010010101')
    assert not evaluate_formula(bundle) and not repeated_boundary_value(C,0,'010',2,'101')
    assert not witness_direct(C,'010010101')
    stats['existing_exceptional_conjugacy_regressions']+=1

    formula=compile_scheme(I,phase);size=validate_formula(formula)
    assert all(x['variable_domain']=='{0,1}*' for x in [formula])
    return {'status':'ALL CHECKS PASSED','seed':SEED,'bounds':bounds,'counts':dict(sorted(stats.items())),
            'formula_example':size,'fractional_power_counterexample':alias,
            'interior_deletion_counterexample':deletion,
            'solver_executed':False,'lean_checked':False,'independent_mathematical_review':False,
            'unrestricted_problem_solved':False,
            'interpretation':'Finite regressions and supplied-assignment checks. No bounded failure is an unrestricted NO.'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',default='checks.json')
    args=p.parse_args();result=check()
    with open(args.output,'w') as h:json.dump(result,h,indent=2);h.write('\n')
    print(json.dumps(result,indent=2))

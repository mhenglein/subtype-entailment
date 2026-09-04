"""Reproducible denial-aware checks; finite experiments are not general proofs."""
from collections import Counter
from dataclasses import replace
from pathlib import Path
import json,random
from border_lab import Instance,words,witness,border_witness,Sandwich
from denial_bridge import build,reduced,Canonical
from safe_extensions import (absorption_holds,safe_states,zero_region,active_rays,advance,
                             extension_decision,branching_certificate,finite_frontier_decision)
from continue_research import encode

ROOT=Path(__file__).resolve().parents[1]
OBSTRUCTION=[('lower',2,0,1),('lower',2,6,1),('lower',2,7,6),('lower',7,2,7),
             ('upper',0,2,3),('upper',3,2,4),('upper',4,4,5),('upper',5,2,2),('denial',2)]


def prefix_filter(I,v):
    """Independent regular filter: exactly the old words starting with v."""
    n=len(v); run=I.run(v); k=len(I.delta)
    delta=[]; labels=[]
    for j,a in enumerate(v):
        target=j+1 if j+1<n else n+run[-1]
        delta.append(tuple(target if b==a else -1 for b in I.alphabet)); labels.append(run[j])
    for q,row in enumerate(I.delta):
        delta.append(tuple(n+r if r>=0 else -1 for r in row)); labels.append(q)
    flags=frozenset((p,q) for p,x in enumerate(labels) for q,y in enumerate(labels) if (x,y) in I.flags)
    return Instance(tuple(delta),frozenset(n+f for f in I.final),flags,
                    frozenset(p for p,q in enumerate(labels) if q in I.bad),0 if n else I.start,I.alphabet)


def main():
    rng=random.Random(2026090424); counts=Counter(); examples=[]; max_full=max_reduced=0
    for case in range(500):
        k=rng.randrange(2,7); C=[]
        for _ in range(rng.randrange(1,2*k+2)):
            op=rng.choice(('lower','upper','upper','leq','denial'))
            arity={'lower':3,'upper':3,'leq':2,'denial':1}[op]
            C.append((op,*(rng.randrange(k) for _ in range(arity))))
        status,B=build(k,C); counts[status]+=1
        if status!='SAT': continue
        I=B.instance; R,classes=reduced(B)
        assert R is not None and absorption_holds(I) and absorption_holds(R)
        max_full=max(max_full,len(I.delta)); max_reduced=max(max_reduced,len(R.delta))
        if len(R.delta)<len(I.delta): counts['smaller_safety_free_DFA']+=1
        front=finite_frontier_decision(R); branch=branching_certificate(R)
        counts['frontier_'+front['status']]+=1
        if front['status']=='YES': assert not Canonical(k,C,0,1,front['word']).errors()
        if branch['status']=='YES':
            counts['branching_YES']+=1
            assert not Canonical(k,C,0,1,branch['word']).errors()
        safe=safe_states(R); zero=zero_region(R)
        for w in words('01',5):
            expected=not Canonical(k,C,0,1,w).errors()
            assert witness(I,w)==witness(R,w)==border_witness(R,w)==expected,(C,w)
            counts['full_reduced_canonical_word_comparisons']+=1
            run=R.run(w)
            # Verify the stronger safety characterization, including all prefixes.
            b_hit=any(B.denials & B.w.run(0,w[:j]) for j in range(len(w)+1))
            s_hit=any(k in B.safety.run(0,w[:j]) for j in range(len(w)+1))
            assert b_hit==s_hit,(C,w)
            counts['safety_elimination_word_comparisons']+=1
            if all(q in safe for q in run) and run[-1] in zero:
                answer=extension_decision(R,w)
                counts['fixed_prefix_'+answer['status']]+=1
                if answer['status']=='NO_EXTENSION':
                    # All flagged strict pairs have difference <=len(w), making
                    # this independently implemented necessary graph exact here.
                    certificate=Sandwich(prefix_filter(R,w),0,len(w)).search(20000)
                    assert certificate['status']=='NO',(C,w,certificate)
                    counts['independent_NO_EXTENSION_certificates']+=1
                if len(w)<=3:
                    for x in words('01',3):
                        rays=active_rays(R,w)
                        for a in x: rays=advance(rays,a)
                        predicted=not rays and all(q in safe for q in R.run(w+x))
                        assert witness(R,w+x)==predicted,(C,w,x)
                        counts['periodic_prediction_comparisons']+=1
        if len(R.delta)<len(I.delta) and len(examples)<3:
            examples.append(dict(k=k,constraints=C,full_states=len(I.delta),reduced_states=len(R.delta)))

    # A real subtype system requiring a repeated pre-absorption state.
    status,B=build(8,OBSTRUCTION); assert status=='SAT'; I,classes=reduced(B)
    shortest=None; local=finite_frontier_decision(I)
    assert local['status']=='UNKNOWN'
    for w in words('01',10):
        exact=w.startswith('11') and w.endswith('1') and len(w)>=4 and set(w[2:-1])=={'0'}
        assert witness(I,w)==exact,(w,exact)
        if exact and shortest is None: shortest=w
        counts['obstruction_language_comparisons']+=1
    assert shortest=='1101' and not Canonical(8,OBSTRUCTION,0,1,shortest).errors()
    assert I.run('11')[-1]==I.run('110')[-1]
    assert not witness(I,'111') and witness(I,'1101')
    # The denial is substantive: dropping it admits the simple earlier path.
    _,without=build(8,[c for c in OBSTRUCTION if c[0]!='denial']); no_denial,_=reduced(without)
    free=finite_frontier_decision(no_denial); assert free['status']=='YES'
    # Empty acceptance boundary and terminal epsilon need separate handling.
    _,terminal=build(3,[('upper',0,2,2),('denial',2)])
    term,_=reduced(terminal)
    assert witness(term,'') and not witness(term,'0') and not witness(term,'1')

    # Abstract examples exercise a nonempty obligation, a genuine periodic NO,
    # and the stronger cyclic-exit (not just branching-SCC) certificate.
    periodic=Instance(((1,3),(2,3),(2,3),(3,3)),frozenset({2,3}),frozenset({(0,1)}),frozenset({3}))
    no=extension_decision(periodic,'00'); assert no['status']=='NO_EXTENSION'
    assert Sandwich(prefix_filter(periodic,'00'),0,2).search()['status']=='NO'
    escape=Instance(((1,4),(2,4),(2,3),(4,4),(4,4)),frozenset({2,3,4}),frozenset({(0,1)}),frozenset({4}))
    cert=branching_certificate(escape)
    assert cert['status']=='YES' and cert['initial_rays']>0 and cert['component']==[2]
    assert cert['word']=='001'

    out=dict(status='PASS',seed=2026090424,generated_systems=500,counts=dict(counts),
             max_full_states=max_full,max_reduced_states=max_reduced,reduction_examples=examples,
             actual_pre_absorption_loop_obstruction=dict(constraints=OBSTRUCTION,instance=encode(I),
                 shortest=shortest,exact_language='11 0^n 1, n>=1',frontier_verdict=local,
                 verdict_without_denial=free),
             periodic_NO_EXTENSION=no,cyclic_exit_certificate=cert,
             scope='Written proofs plus bounded independent comparisons; not Lean-checked; no unrestricted decision claim')
    (ROOT/'results/unrestricted-continuation.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('reduction_examples','actual_pre_absorption_loop_obstruction')},indent=2))

if __name__=='__main__': main()

"""Independent checks for the infinite-safe-continuation decision, not a full solver."""
from collections import Counter
from itertools import product
from pathlib import Path
import json, random
from border_lab import Instance,words,witness,border_witness
from safe_extensions import safe_states,zero_region,shortest_paths,primitive,active_rays,finite_frontier_decision,components
from infinite_extensions import (infinite_extension_decision,monitor_start,monitor_step,
                                 pure_period,periodic_prefix_search)
from denial_bridge import build,reduced,Canonical
from check_unrestricted_continuation import OBSTRUCTION

ROOT=Path(__file__).resolve().parents[1]

def infinite_states(I):
    safe=safe_states(I); recurrent=set()
    for part in components(I,safe):
        if len(part)>1 or any(q in I.delta[q] for q in part): recurrent.update(part)
    reverse={q:set() for q in safe}
    for q in safe:
        for r in I.delta[q]:
            if r in safe: reverse[r].add(q)
    todo=list(recurrent)
    for q in todo:
        for r in reverse[q]:
            if r not in recurrent: recurrent.add(r); todo.append(r)
    return recurrent

def random_absorbing(rng,k):
    zero={q for q in range(k) if rng.random()<.3}
    if not zero: zero={k-1}
    finals=zero|{q for q in range(k) if rng.random()<.2}
    delta=tuple(tuple(rng.choice([-1]+sorted(zero)) if q in finals else rng.randrange(-1,k)
                      for _ in '01') for q in range(k))
    flags=frozenset((q,r) for q in range(k) for r in range(k) if r not in zero and rng.random()<.2)
    return Instance(delta,frozenset(finals),flags,frozenset(q for q in range(k) if rng.random()<.1))

def main():
    rng=random.Random(2026090429); counts=Counter(); example=None
    periods=sorted({primitive(w) for w in words('01',3) if w})
    for case in range(1500):
        k=rng.randrange(2,8); I=random_absorbing(rng,k); safe=safe_states(I); zero=zero_region(I)
        inf=infinite_states(I); answer=infinite_extension_decision(I,100000)
        counts['abstract_'+answer['status']]+=1
        if answer['status']=='YES':
            assert witness(I,answer['word']) and border_witness(I,answer['word'])
            assert I.run(answer['word'])[-1] in inf
            counts['method_'+answer['method']]+=1
            if example is None and answer['method']=='finite periodic suffix monitor' and finite_frontier_decision(I)['status']=='UNKNOWN':
                example=dict(instance=dict(delta=I.delta,final=sorted(I.final),flags=sorted(I.flags),bad=sorted(I.bad)),answer=answer)
        found=False
        for w in words('01',6):
            run=I.run(w)
            if run is None or any(q not in safe for q in run): continue
            if witness(I,w) and run[-1] in inf:
                found=True; assert answer['status']!='NO_INFINITE_EXTENSION',(I,w,answer)
            if run[-1] not in zero: continue
            rays=active_rays(I,w)
            for p in periods:
                offset=len(w)%len(p); state=monitor_start(I,len(p))
                for a in w: state=monitor_step(I,p,offset,state,a)
                assert state is not None and state[1]==offset
                assert state[3]==(p in rays),(I,w,p,state,rays)
                counts['monitor_identity_comparisons']+=1
        if k<=3:
            # The proved six-letter bound applies after removing finals unable
            # to continue infinitely. Witness flags and run semantics unchanged.
            assert (answer['status']=='YES')==found,(I,answer,found)
            counts['exact_small_state_decisions']+=1
    for case in range(400):
        k=rng.randrange(2,7); C=[]
        for _ in range(rng.randrange(1,2*k+2)):
            op=rng.choice(('lower','upper','upper','leq','denial'))
            arity={'lower':3,'upper':3,'leq':2,'denial':1}[op]
            C.append((op,*(rng.randrange(k) for _ in range(arity))))
        status,B=build(k,C); counts['actual_'+status]+=1
        if status!='SAT': continue
        I,_=reduced(B); answer=infinite_extension_decision(I)
        counts['actual_decision_'+answer['status']]+=1
        if answer['status']=='YES':
            assert not Canonical(k,C,0,1,answer['word']).errors()
            assert I.run(answer['word'])[-1] in infinite_states(I)
        for w in words('01',5):
            if witness(I,w) and I.run(w)[-1] in infinite_states(I):
                assert answer['status']!='NO_INFINITE_EXTENSION'
            counts['actual_word_comparisons']+=1
    _,B=build(8,OBSTRUCTION); I,_=reduced(B)
    obstruction=infinite_extension_decision(I)
    assert obstruction['status']=='NO_INFINITE_EXTENSION' and witness(I,'1101')
    # A fixed periodic tail can leave an unavoidable flagged comparison.
    pure=Instance(((1,-1),(2,-1),(2,-1)),frozenset({2}),frozenset({(0,1)}))
    assert infinite_extension_decision(pure)['status']=='NO_INFINITE_EXTENSION'
    # A nonpure tail avoids every purely periodic pending prediction.
    nonpure=Instance(((1,-1),(2,-1),(3,-1),(-1,3)),frozenset({2,3}),frozenset({(0,1)}))
    nonpure_answer=infinite_extension_decision(nonpure)
    assert nonpure_answer['status']=='YES'
    assert pure_period('0','1') is None
    assert pure_period('0','10')=='01'
    assert pure_period('01','01')=='01'
    out=dict(status='PASS',seed=2026090429,abstract_instances=1500,generated_actual_systems=400,
             counts=dict(counts),finite_terminal_obstruction=obstruction,
             periodic_monitor_loop_example=example,nonpure_example=nonpure_answer,
             scope='Exact theorem for infinite-safe-continuation witnesses; NO_INFINITE_EXTENSION is not unrestricted NO; written proofs not Lean-checked')
    (ROOT/'results/infinite-extensions.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()

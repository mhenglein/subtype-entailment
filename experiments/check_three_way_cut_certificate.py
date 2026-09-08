"""Regression for exact and automatically synthesized three-way NO certificates."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance
from three_way_cut_certificate import (DFA, ThreeWayCertificate,
    verify_three_way_certificate, discover_three_way_certificate)


def barrier_instance():
    return Instance(((1,2),(1,2),(3,-1),(3,4),(5,2),(-1,-1)),
                    frozenset({5}),frozenset({(0,2),(0,3),(1,2)}))


def barrier_middle():
    return DFA(((1,-1),(1,2),(-1,0)),frozenset({0}))


def periodic_multieffect_instance():
    delta=((0,1),(2,-1),(3,4),(3,5),(6,7),(6,-1),(-1,-1),(3,-1))
    flags=frozenset({(0,1),(0,2),(0,3),(0,7)})
    return Instance(delta,frozenset({6}),flags)


def periodic_middle():
    return DFA(((1,-1),(-1,2),(-1,3),(-1,-1)),frozenset({0,3}))


def direct_accepts(I,w):
    run=I.run(w)
    return run is not None and run[-1] in I.final


def middle_accepts(M,w):
    q=M.start
    for a in w:
        q=M.step(q,int(a))
        if q<0:return False
    return q in M.final


def family_accepts(M,w):
    for first in range(len(w)+1):
        if any(c!='0' for c in w[:first]): continue
        if first>=len(w) or w[first]!='1': continue
        for cut in range(first+1,len(w)+1):
            if not middle_accepts(M,w[first+1:cut]): continue
            tail=w[cut:]
            if len(tail)>=3 and tail.endswith('10') and set(tail[:-2])<= {'0'} and tail[:-2]:
                return True
    return False


def bounded_language_check(I,M,max_len):
    checked=0
    for n in range(max_len+1):
        for bits in product('01',repeat=n):
            w=''.join(bits)
            assert direct_accepts(I,w)==family_accepts(M,w)
            checked+=1
    return checked


def main():
    I=barrier_instance(); M=barrier_middle(); cert=ThreeWayCertificate(0,1,M)
    out=verify_three_way_certificate(I,cert)
    assert out['status']=='VERIFIED_NO'
    automatic=discover_three_way_certificate(I)
    assert automatic['status']=='VERIFIED_NO' and automatic['a']==0
    bounded=bounded_language_check(I,M,14)

    rejected=[]
    for flag in sorted(I.flags):
        J=Instance(I.delta,I.final,I.flags-{flag},I.bad,I.start,I.alphabet)
        bad=verify_three_way_certificate(J,cert)
        assert bad['status']=='NOT_APPLICABLE'
        assert discover_three_way_certificate(J)['status']=='INCONCLUSIVE'
        rejected.append(flag)

    M_bad=DFA(((1,-1),(1,2),(-1,0)),frozenset({0,2}))
    bad=verify_three_way_certificate(I,ThreeWayCertificate(0,1,M_bad))
    assert bad['status']=='NOT_APPLICABLE'

    P=periodic_multieffect_instance(); PM=periodic_middle()
    periodic=verify_three_way_certificate(P,ThreeWayCertificate(0,1,PM))
    assert periodic['status']=='VERIFIED_NO'
    auto_periodic=discover_three_way_certificate(P)
    assert auto_periodic['status']=='VERIFIED_NO' and auto_periodic['a']==0
    effects=periodic['middle_effects']
    assert {row['middle_effect'] for row in effects}=={1,7}
    assert max(len(row['trailing_orbit']) for row in effects)==2
    periodic_checks=bounded_language_check(P,PM,14)

    # Positive instance: automatic synthesis must not manufacture a NO proof.
    positive=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert discover_three_way_certificate(positive)['status']=='INCONCLUSIVE'

    result={'status':'PASS','certificate_status':out['status'],
            'automatic_barrier_status':automatic['status'],
            'bounded_independent_language_checks':bounded,
            'required_flag_mutations_rejected':len(rejected),
            'bad_middle_rejected':True,
            'positive_instance_rejected_by_synthesizer':True,
            'periodic_multieffect':{
              'status':periodic['status'],
              'automatic_status':auto_periodic['status'],
              'middle_effects':len(effects),
              'leading_orbit_states':len(periodic['leading_positive_orbit']),
              'max_trailing_orbit_states':max(len(row['trailing_orbit']) for row in effects),
              'bounded_language_checks':periodic_checks},
            'scope':'Exact finite verifier plus automatic synthesis for a* b M a+ b a with finite effects/orbits',
            'proof_status':'Verifier/synthesizer checks all regular-language/orbit premises exactly; theorem proof recorded separately; not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'three-way-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()

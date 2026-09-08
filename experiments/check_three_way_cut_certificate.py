"""Regression for the exact three-way regular-middle NO certificate."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance
from three_way_cut_certificate import DFA, ThreeWayCertificate, verify_three_way_certificate


def barrier_instance():
    return Instance(((1,2),(1,2),(3,-1),(3,4),(5,2),(-1,-1)),
                    frozenset({5}),frozenset({(0,2),(0,3),(1,2)}))


def barrier_middle():
    # M=(0+11)*. State 0 is a block boundary, state 1 is 0+, state 2 has
    # consumed the first 1 and requires the second 1.
    return DFA(((1,-1),(1,2),(-1,0)),frozenset({0}))


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
    # Independent bounded parser for the regression only; exact language
    # equality is checked internally by finite symmetric difference.
    for first in range(len(w)+1):
        if any(c!='0' for c in w[:first]): continue
        if first>=len(w) or w[first]!='1': continue
        for cut in range(first+1,len(w)+1):
            if not middle_accepts(M,w[first+1:cut]): continue
            tail=w[cut:]
            if len(tail)>=3 and tail.endswith('10') and set(tail[:-2])<= {'0'} and tail[:-2]:
                return True
    return False


def main():
    I=barrier_instance(); M=barrier_middle(); cert=ThreeWayCertificate(0,1,M)
    out=verify_three_way_certificate(I,cert)
    assert out['status']=='VERIFIED_NO'
    bounded=0
    for n in range(15):
        for bits in product('01',repeat=n):
            w=''.join(bits)
            assert direct_accepts(I,w)==family_accepts(M,w)
            bounded+=1

    # Each fixed flag is genuinely necessary to this proof object.
    rejected=[]
    for flag in sorted(I.flags):
        J=Instance(I.delta,I.final,I.flags-{flag},I.bad,I.start,I.alphabet)
        bad=verify_three_way_certificate(J,cert)
        assert bad['status']=='NOT_APPLICABLE'
        rejected.append(flag)

    # The exact-language guard rejects a superficially similar but enlarged
    # middle language: 1 is now accepted, which would admit words outside I.
    M_bad=DFA(((1,-1),(1,2),(-1,0)),frozenset({0,2}))
    bad=verify_three_way_certificate(I,ThreeWayCertificate(0,1,M_bad))
    assert bad['status']=='NOT_APPLICABLE'

    result={'status':'PASS','certificate_status':out['status'],
            'bounded_independent_language_checks':bounded,
            'required_flag_mutations_rejected':len(rejected),
            'bad_middle_rejected':True,
            'scope':'Exact finite verifier for a* b M a+ b a three-way-cut NO certificates',
            'proof_status':'Verifier checks all regular-language premises exactly; theorem proof recorded separately; not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'three-way-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()

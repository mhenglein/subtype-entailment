"""Regression for orbit-split three-way NO certificates."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance, witness, words
from orbit_split_cut_certificate import discover_orbit_split_certificate
from three_way_cut_certificate import discover_three_way_certificate


def parity_split_instance():
    # Accepted language: 0* 1 0+ 1 0. The first 1 reaches anchor 2 or 3
    # depending on parity of the leading 0-run, so the old single-anchor
    # certificate cannot apply. All source states 0/1 are flagged to every
    # possible middle/trailing state 2..5.
    delta=((1,2),(0,3),(4,-1),(5,-1),(5,6),(4,6),(7,-1),(-1,-1))
    flags=frozenset((p,q) for p in (0,1) for q in (2,3,4,5))
    return Instance(delta,frozenset({7}),flags)


def language_formula(w):
    if len(w)<4 or not w.endswith('10'): return False
    first=w.find('1')
    if first<0 or any(c!='0' for c in w[:first]): return False
    middle=w[first+1:-2]
    return bool(middle) and all(c=='0' for c in middle)


def bounded_language_checks(I,max_len=13):
    checked=0
    for n in range(max_len+1):
        for bits in product('01',repeat=n):
            w=''.join(bits)
            accepted=I.admissible(w)
            assert accepted==language_formula(w),(w,accepted)
            if accepted: assert not witness(I,w)
            checked+=1
    return checked


def main():
    I=parity_split_instance()
    old=discover_three_way_certificate(I)
    assert old['status']=='INCONCLUSIVE'
    new=discover_orbit_split_certificate(I)
    assert new['status']=='VERIFIED_NO' and new['a']==0
    verification=new['verification']
    assert len(set(verification['anchors'].values()))==2
    checked=bounded_language_checks(I)

    # Every required flag is semantically used by the finite proof object.
    rejected=0
    for flag in verification['required_flags']:
        J=Instance(I.delta,I.final,I.flags-{tuple(flag)},I.bad,I.start,I.alphabet)
        if discover_orbit_split_certificate(J)['status']!='VERIFIED_NO':
            rejected+=1
    assert rejected==len(verification['required_flags'])

    # Positive control: the recurrent-target YES fixture must stay inconclusive.
    positive=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert discover_orbit_split_certificate(positive)['status']=='INCONCLUSIVE'

    result={'status':'PASS','old_status':old['status'],'new_status':new['status'],
            'leading_states':len(verification['leading_states']),
            'distinct_anchors':len(set(verification['anchors'].values())),
            'required_flags':len(verification['required_flags']),
            'required_flag_mutations_rejected':rejected,
            'bounded_language_and_no_checks':checked,
            'positive_control':'INCONCLUSIVE',
            'scope':'Exact all-length orbit-split family; finite bounded checks are regression only',
            'proof_status':'Finite-language equivalence/orbit premises verified exactly; written theorem not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'orbit-split-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

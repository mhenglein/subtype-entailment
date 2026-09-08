"""Regression for orbit/residue-split three-way NO certificates."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance, witness
from orbit_split_cut_certificate import discover_orbit_split_certificate
from three_way_cut_certificate import discover_three_way_certificate


def parity_split_instance():
    # Accepted language: 0* 1 0+ 1 0. The first 1 reaches anchor 2 or 3
    # depending on parity of the leading 0-run.
    delta=((1,2),(0,3),(4,-1),(5,-1),(5,6),(4,6),(7,-1),(-1,-1))
    flags=frozenset((p,q) for p in (0,1) for q in (2,3,4,5))
    return Instance(delta,frozenset({7}),flags)


def even_leading_instance():
    # Same trailing language, but the delimiter is defined only on even leading
    # 0-lengths. N={2t:t>=0} is a genuine ultimately-periodic parameter set.
    delta=((1,2),(0,-1),(4,-1),(5,-1),(5,6),(4,6),(7,-1),(-1,-1))
    flags=frozenset((p,q) for p in (0,1) for q in (2,4,5))
    return Instance(delta,frozenset({7}),flags)


def language_formula(w,even_only=False):
    if len(w)<4 or not w.endswith('10'): return False
    first=w.find('1')
    if first<0 or any(c!='0' for c in w[:first]): return False
    if even_only and first%2: return False
    middle=w[first+1:-2]
    return bool(middle) and all(c=='0' for c in middle)


def bounded_language_checks(I,max_len=13,even_only=False):
    checked=0
    for n in range(max_len+1):
        for mask in range(1<<n):
            w=''.join('1' if mask>>i&1 else '0' for i in reversed(range(n)))
            accepted=I.admissible(w)
            assert accepted==language_formula(w,even_only),(w,accepted)
            if accepted: assert not witness(I,w)
            checked+=1
    return checked


def mutation_check(I,verification):
    rejected=0
    for flag in verification['required_flags']:
        J=Instance(I.delta,I.final,I.flags-{tuple(flag)},I.bad,I.start,I.alphabet)
        if discover_orbit_split_certificate(J)['status']!='VERIFIED_NO': rejected+=1
    assert rejected==len(verification['required_flags'])
    return rejected


def main():
    I=parity_split_instance(); old=discover_three_way_certificate(I)
    assert old['status']=='INCONCLUSIVE'
    new=discover_orbit_split_certificate(I); assert new['status']=='VERIFIED_NO' and new['a']==0
    v=new['verification']; assert len(set(v['anchors'].values()))==2
    checked=bounded_language_checks(I); rejected=mutation_check(I,v)

    E=even_leading_instance(); old_even=discover_three_way_certificate(E)
    assert old_even['status']=='INCONCLUSIVE'
    even=discover_orbit_split_certificate(E); assert even['status']=='VERIFIED_NO' and even['a']==0
    ev=even['verification']; assert len(ev['leading_trajectory'])==2 and len(ev['active_leading_states'])==1
    even_checked=bounded_language_checks(E,even_only=True)

    positive=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert discover_orbit_split_certificate(positive)['status']=='INCONCLUSIVE'

    result={'status':'PASS','parity_split':{
              'old_status':old['status'],'new_status':new['status'],
              'leading_trajectory_states':len(v['leading_trajectory']),
              'active_leading_states':len(v['active_leading_states']),
              'distinct_anchors':len(set(v['anchors'].values())),
              'required_flags':len(v['required_flags']),
              'required_flag_mutations_rejected':rejected,
              'bounded_language_and_no_checks':checked},
            'even_residue':{
              'old_status':old_even['status'],'new_status':even['status'],
              'leading_trajectory_states':len(ev['leading_trajectory']),
              'active_leading_states':len(ev['active_leading_states']),
              'bounded_language_and_no_checks':even_checked},
            'positive_control':'INCONCLUSIVE',
            'scope':'Exact all-length orbit/residue-split family; bounded checks are regression only',
            'proof_status':'Language equality and finite orbit premises verified exactly; written theorem not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'orbit-split-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

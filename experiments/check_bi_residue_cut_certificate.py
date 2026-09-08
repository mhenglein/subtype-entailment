"""Regression and exact-small-census coverage for bi-residue NO certificates."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance, witness
from bi_residue_cut_certificate import discover_bi_residue_certificate
from orbit_split_cut_certificate import discover_orbit_split_certificate
from three_way_cut_certificate import discover_three_way_certificate
from three_state_decision import three_state_decision


def odd_trailing_instance():
    delta=((0,1),(2,-1),(3,4),(2,-1),(5,-1),(-1,-1))
    flags=frozenset({(0,1),(0,2),(0,3)})
    return Instance(delta,frozenset({5}),flags)


def formula(w):
    if len(w)<4 or not w.endswith('10'): return False
    first=w.find('1')
    if first<0 or any(c!='0' for c in w[:first]): return False
    run=w[first+1:-2]
    return bool(run) and all(c=='0' for c in run) and len(run)%2==1


def bounded_checks(I,max_len=14):
    checked=accepted=0
    for n in range(max_len+1):
        for bits in product('01',repeat=n):
            w=''.join(bits); direct=I.admissible(w)
            assert direct==formula(w),(w,direct)
            if direct:
                accepted+=1; assert not witness(I,w)
            checked+=1
    return checked,accepted


def exact_small_census():
    total=no=old_count=orbit_count=bi_count=0
    strict_gains=bi_over_orbit=0
    for k in range(1,4):
        possible=[(p,q) for p in range(k-1) for q in range(k-1) if p!=q]
        for raw in product(range(-1,k),repeat=2*(k-1)):
            delta=tuple(tuple(raw[2*p:2*p+2]) for p in range(k-1))+((-1,-1),)
            for mask in range(1<<len(possible)):
                flags=frozenset(pair for i,pair in enumerate(possible) if mask>>i&1)
                I=Instance(delta,frozenset({k-1}),flags); total+=1
                exact=three_state_decision(I)
                old=discover_three_way_certificate(I)['status']=='VERIFIED_NO'
                orbit=discover_orbit_split_certificate(I)['status']=='VERIFIED_NO'
                bi=discover_bi_residue_certificate(I)['status']=='VERIFIED_NO'
                if old:
                    assert exact['status']=='NO'; old_count+=1
                if orbit:
                    assert exact['status']=='NO'; orbit_count+=1
                if bi:
                    assert exact['status']=='NO'; bi_count+=1
                if exact['status']=='NO': no+=1
                if orbit and not old: strict_gains+=1
                if bi and not orbit: bi_over_orbit+=1
    return {'instances':total,'exact_no':no,'old_three_way_no':old_count,
            'orbit_split_no':orbit_count,'bi_residue_no':bi_count,
            'orbit_strict_gains':strict_gains,'bi_residue_strict_gains':bi_over_orbit}


def main():
    I=odd_trailing_instance()
    old=discover_three_way_certificate(I); orbit=discover_orbit_split_certificate(I)
    assert old['status']==orbit['status']=='INCONCLUSIVE'
    new=discover_bi_residue_certificate(I)
    assert new['status']=='VERIFIED_NO' and new['a']==0
    v=new['verification']
    residue_states=sorted({tuple(row['terminal_residue_states'])
                           for branch in v['branches'] for row in branch['effects']})
    checked,accepted=bounded_checks(I)

    rejected=0
    for flag in v['required_flags']:
        J=Instance(I.delta,I.final,I.flags-{tuple(flag)},I.bad,I.start,I.alphabet)
        if discover_bi_residue_certificate(J)['status']!='VERIFIED_NO': rejected+=1
    assert rejected==len(v['required_flags'])

    positive=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert discover_bi_residue_certificate(positive)['status']=='INCONCLUSIVE'
    census=exact_small_census()

    result={'status':'PASS','old_three_way':old['status'],
            'orbit_split':orbit['status'],'bi_residue':new['status'],
            'leading_trajectory_states':len(v['leading_trajectory']),
            'tail_capable_states':len(v['tail_capable_states']),
            'terminal_residue_state_patterns':[list(x) for x in residue_states],
            'required_flags':len(v['required_flags']),
            'required_flag_mutations_rejected':rejected,
            'bounded_language_and_no_checks':checked,'bounded_accepted_words':accepted,
            'exact_small_census':census,'positive_control':'INCONCLUSIVE',
            'scope':'All-length bi-residue certificate; <=3-state census uses independent exact theorem only to measure coverage',
            'proof_status':'Exact finite language/orbit verifier; written theorem not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'bi-residue-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

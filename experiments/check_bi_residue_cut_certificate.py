"""Regression for two-parameter ultimately-periodic NO certificates."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance, witness
from bi_residue_cut_certificate import discover_bi_residue_certificate
from orbit_split_cut_certificate import discover_orbit_split_certificate
from three_way_cut_certificate import discover_three_way_certificate


def odd_trailing_instance():
    # Language: 0* 1 0^(2t+1) 1 0. The trailing zero count is genuinely
    # periodic: after the first mandatory zero, controls 2/3 alternate and only
    # state 2 has the terminal 1-edge.
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


def main():
    I=odd_trailing_instance()
    old=discover_three_way_certificate(I)
    orbit=discover_orbit_split_certificate(I)
    assert old['status']=='INCONCLUSIVE'
    assert orbit['status']=='INCONCLUSIVE'
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

    result={'status':'PASS','old_three_way':old['status'],
            'orbit_split':orbit['status'],'bi_residue':new['status'],
            'leading_trajectory_states':len(v['leading_trajectory']),
            'tail_capable_states':len(v['tail_capable_states']),
            'terminal_residue_state_patterns':[list(x) for x in residue_states],
            'required_flags':len(v['required_flags']),
            'required_flag_mutations_rejected':rejected,
            'bounded_language_and_no_checks':checked,
            'bounded_accepted_words':accepted,
            'positive_control':'INCONCLUSIVE',
            'scope':'Exact all-length bi-residue family; bounded enumeration is differential evidence only',
            'proof_status':'Exact finite language/orbit verifier; written theorem not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'bi-residue-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

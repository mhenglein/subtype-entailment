"""Regression for fixed-word-period three-way NO certificates."""
import json
from itertools import product
from pathlib import Path

from border_lab import Instance, witness
from three_way_cut_certificate import DFA, discover_three_way_certificate
from orbit_split_cut_certificate import discover_orbit_split_certificate
from bi_residue_cut_certificate import discover_bi_residue_certificate
from word_period_cut_certificate import WordPeriodCertificate, verify_word_period_certificate


def period01_instance():
    # Exact language (01)^n 1 (01)^m 1 01, n>=0,m>=1.
    # P=01 is genuinely non-unary. One flag (0,2) covers all three cases
    # because both P-actions are loops at their respective boundaries.
    delta=((1,2),( -1,0),(3,4),(-1,2),(5,-1),(-1,6),(-1,-1))
    return Instance(delta,frozenset({6}),frozenset({(0,2)}))


def middle_epsilon_dfa():
    return DFA(((-1,-1),),frozenset({0}),0)


def formula(w):
    P='01'; B='1'
    # Direct finite parser for P* B P+ B P.
    for n in range(len(w)//2+1):
        pref=P*n+B
        if not w.startswith(pref): continue
        rest=w[len(pref):]
        for m in range(1,len(rest)//2+1):
            if rest==P*m+B+P: return True
    return False


def bounded_checks(I,max_len=16):
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
    I=period01_instance(); cert=WordPeriodCertificate('01','1',middle_epsilon_dfa())
    out=verify_word_period_certificate(I,cert)
    assert out['status']=='VERIFIED_NO'
    # All installed unary arithmetic recognizers should remain inconclusive.
    old=discover_three_way_certificate(I)['status']
    orbit=discover_orbit_split_certificate(I)['status']
    bi=discover_bi_residue_certificate(I)['status']
    assert old==orbit==bi=='INCONCLUSIVE',(old,orbit,bi)
    checked,accepted=bounded_checks(I)

    J=Instance(I.delta,I.final,frozenset(),I.bad,I.start,I.alphabet)
    assert verify_word_period_certificate(J,cert)['status']=='NOT_APPLICABLE'
    # Positive control: removing the only flag leaves accepted witnesses.
    assert any(witness(J,'01'*n+'1'+'01'*m+'1'+'01') for n in range(3) for m in range(1,4))

    result={'status':'PASS','period':'01','delimiter':'1',
            'word_period_status':out['status'],'old_three_way':old,
            'orbit_split':orbit,'bi_residue':bi,
            'required_flags':len(out['required_flags']),
            'bounded_language_and_no_checks':checked,'bounded_accepted_words':accepted,
            'missing_flag_control':'NOT_APPLICABLE',
            'scope':'Exact all-length fixed-word-period family; bounded enumeration is regression only',
            'proof_status':'Exact candidate-language equality/orbit verifier; written theorem not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'word-period-cut-certificate.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

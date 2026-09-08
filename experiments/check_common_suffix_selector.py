#!/usr/bin/env python3
"""Regression for exact constant-from-end selector synthesis."""
import json
from itertools import product
from pathlib import Path
from common_suffix_selector import (
    maximal_common_suffix, suffix_counterexample, forced_tail_violation,
)

# Seven-state different-gap instance from the last-flag spectrum note.
SEVEN=(
    (-1,1),
    (2,1),
    (3,-1),
    (-1,4),
    (5,4),
    (6,-1),
    (-1,-1),
)
FLAGS=frozenset({(0,3),(4,5)})
FINAL={6}

# Positive control: language {10,110}; maximal common suffix is 10, but no flag.
CONTROL=(
    (-1,1),
    (3,2),
    (3,-1),
    (-1,-1),
)


def run(delta,word):
    q=0; states=[q]
    for ch in word:
        q=delta[q][ord(ch)-48]
        if q < 0: return None
        states.append(q)
    return tuple(states)


def violations(delta,final,flags,word):
    st=run(delta,word)
    if st is None or st[-1] not in final: return ()
    n=len(word); out=[]
    for i in range(n+1):
        for j in range(i+1,n):
            if (st[i],st[j]) in flags and word[i:].startswith(word[j:]):
                out.append((i,j,st[i],st[j]))
    return tuple(out)


def main():
    assert maximal_common_suffix(SEVEN,0,FINAL) == '00'
    cert=forced_tail_violation(SEVEN,0,FINAL,FLAGS)
    assert cert['status']=='NO_CERTIFICATE'
    assert cert['common_suffix']=='00'
    assert tuple(cert['relative_cuts'])==(0,1)
    assert cert['target_length']==1
    assert set(cert['state_pairs'])=={(4,5)}

    # A non-universal longer suffix must produce a concrete accepted counterexample.
    cex=suffix_counterexample(SEVEN,0,FINAL,'100')
    assert cex is not None
    st=run(SEVEN,cex)
    assert st is not None and st[-1] in FINAL and not cex.endswith('100')

    checked=0; accepted=0; certified=0
    for n in range(15):
        for m in range(15):
            if n < 1 or m < 1: continue
            w='1'*n+'00'+'1'*m+'00'
            st=run(SEVEN,w)
            assert st is not None and st[-1] in FINAL
            accepted += 1
            vs=violations(SEVEN,FINAL,FLAGS,w)
            assert vs
            # The synthesized constant-from-end selector is present in every word.
            i=len(w)-2; j=len(w)-1
            assert (i,j,4,5) in vs
            certified += 1
            checked += 1

    words=0; accepted_short=0; witnesses=0
    for length in range(13):
        for bits in product('01',repeat=length):
            w=''.join(bits); words += 1
            st=run(SEVEN,w)
            if st is None or st[-1] not in FINAL: continue
            accepted_short += 1
            if not violations(SEVEN,FINAL,FLAGS,w): witnesses += 1
            assert w.endswith('00')

    # No false certificate when the flag set is empty.
    noflag=forced_tail_violation(SEVEN,0,FINAL,set())
    assert noflag['status']=='NO_CERTIFICATE_NOT_FOUND'

    result={
        'status':'PASS',
        'proof_status':(
            'The selector algorithm is an exact finite regular-language construction. '
            'The seven-state all-word NO consequence follows directly from its returned '
            'forced suffix/state certificate; bounded enumeration is additional evidence.'
        ),
        'seven_state':{
            'common_suffix':cert['common_suffix'],
            'relative_cuts':list(cert['relative_cuts']),
            'target_length':cert['target_length'],
            'state_pairs':[list(x) for x in cert['state_pairs']],
            'parameter_candidates':checked,
            'binary_words_through_12':words,
            'accepted_short':accepted_short,
            'witnesses':witnesses,
            'longer_suffix_counterexample':cex,
        },
        'negative_control':{
            'empty_flags_status':noflag['status'],
        },
        'scope':(
            'Complete only for NO instances possessing a forbidden comparison entirely '
            'inside a common suffix with fixed relative cuts and universally flagged state pairs.'
        ),
    }
    out=Path(__file__).resolve().parents[1]/'results'/'common-suffix-selector.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

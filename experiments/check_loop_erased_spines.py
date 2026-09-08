#!/usr/bin/env python3
"""Regression for the exact finite simple-spine / regular-return cover."""
import json
from itertools import product
from pathlib import Path
from loop_erased_spines import (
    verify_decomposition, simple_accepting_spines, spine_key, run,
)

BENCH=(
    (1,2),
    (1,2),
    (3,-1),
    (3,4),
    (5,2),
    (-1,-1),
)
FINAL={5}


def main():
    spines=simple_accepting_spines(BENCH,0,FINAL)
    keys={(x['states'],x['edges']) for x in spines}

    # The direct core of the six-state benchmark is one finite simple spine.
    assert ((0,2,3,4,5),('1','0','1','0')) in keys

    words=0; accepted=0; decomposed=0; max_returns=0; seen_keys=set()
    for length in range(15):
        for bits in product('01',repeat=length):
            w=''.join(bits); words += 1
            st=run(BENCH,0,w)
            if st is None or st[-1] not in FINAL: continue
            accepted += 1
            parts=verify_decomposition(BENCH,0,w,FINAL)
            key=spine_key(parts)
            assert key in keys
            seen_keys.add(key)
            decomposed += 1
            max_returns=max(max_returns,len(parts['returns']))

    # Structured nonflat family: every arbitrary recurrent middle is absorbed
    # into a return word at one of finitely many simple-spine states.
    structured=0
    for n in range(8):
        for m in range(1,8):
            for r1 in range(1,5):
                for r2 in range(1,4):
                    w='0'*n+'1'+'0'*r1+'11'+'0'*r2+'11'+'0'*m+'10'
                    st=run(BENCH,0,w)
                    assert st is not None and st[-1] in FINAL
                    parts=verify_decomposition(BENCH,0,w,FINAL)
                    assert spine_key(parts) in keys
                    structured += 1

    # Small exhaustive sanity census across every two-state partial binary table
    # with accepting state 1.  This validates the factorization independently of
    # the benchmark's shape.
    tables=0; generic_words=0
    choices=(-1,0,1)
    for flat in product(choices,repeat=4):
        delta=(flat[:2],flat[2:])
        sp=simple_accepting_spines(delta,0,{1})
        keys2={(x['states'],x['edges']) for x in sp}
        tables += 1
        for length in range(7):
            for bits in product('01',repeat=length):
                w=''.join(bits)
                st=run(delta,0,w)
                if st is None or st[-1]!=1: continue
                parts=verify_decomposition(delta,0,w,{1})
                assert spine_key(parts) in keys2
                generic_words += 1

    result={
        'status':'PASS',
        'proof_status':(
            'Exact path factorization theorem by last occurrences; finite tests are '
            'supporting implementation evidence only. BorderAvoid decidability does '
            'not follow from the cover alone.'
        ),
        'benchmark':{
            'simple_spines':len(spines),
            'binary_words_through_14':words,
            'accepted':accepted,
            'decomposed':decomposed,
            'observed_spines':len(seen_keys),
            'max_return_variables':max_returns,
            'structured_nonflat':structured,
        },
        'generic_two_state':{
            'tables':tables,
            'accepted_words_checked':generic_words,
        },
        'scope':(
            'Exact finite language cover by simple labelled spines and regular '
            'state-return variables. The remaining problem is comparison interaction '
            'between those variables.'
        ),
    }
    out=Path(__file__).resolve().parents[1]/'results'/'loop-erased-spines.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

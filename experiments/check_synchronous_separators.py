"""Independent checks for synchronous-separator preprocessing."""
from itertools import product
import json
from pathlib import Path

from border_lab import Instance, border_witness, witness, words
from marker_certificate import marker_decision
from target_frontier import Limits as FrontierLimits
from synchronous_separators import (compile_separators, encode_word,
    separator_certificate, separator_decision, frontier_separator_certificate,
    frontier_separator_decision)

UNCAPPED = FrontierLimits(states=None, transitions=None, descriptors=None,
                          schemas=None, reconstruction=None)
CENSUS_LIMITS = FrontierLimits(states=20000, transitions=100000,
                               descriptors=20000, schemas=1000,
                               reconstruction=50000)


def uniform_code(I):
    k=len(I.delta); table=[]
    for p in range(k):
        table.append((k+I.delta[p][0] if I.delta[p][0]>=0 else -1,
                      k+I.delta[p][1] if I.delta[p][1]>=0 else -1))
    table.extend((q,-1) for q in range(k))
    return Instance(tuple(table),I.final,I.flags,I.bad,I.start)


def check_equivalence(I,maximum,frontier=False):
    summary,cert=(frontier_separator_certificate(I) if frontier else separator_certificate(I))
    if cert is None: return 0
    J=compile_separators(I,cert); count=0
    for w in words('01',maximum):
        if I.run(w) is None: continue
        ew=encode_word(I,w,cert)
        assert I.admissible(w)==J.admissible(ew)
        assert witness(I,w)==witness(J,ew)
        assert border_witness(I,w)==border_witness(J,ew)
        count += 1
    return count


def small_census():
    instances=certified=comparisons=yes=no=unknown=frontier_extra=frontier_capped=0
    for k in range(1,4):
        possible=[(p,q) for p in range(k-1) for q in range(k-1) if p!=q]
        for raw in product(range(-1,k),repeat=2*(k-1)):
            delta=tuple(tuple(raw[2*p:2*p+2]) for p in range(k-1))+((-1,-1),)
            for mask in range(1<<len(possible)):
                flags=frozenset(pair for i,pair in enumerate(possible) if mask>>i&1)
                I=Instance(delta,frozenset({k-1}),flags); instances += 1
                summary,cert=separator_certificate(I)
                if cert is None:
                    unknown += 1
                    out=frontier_separator_decision(I,CENSUS_LIMITS)
                    if out['status'] in ('YES','NO'):
                        frontier_extra += 1
                        if out['status']=='YES': assert witness(I,out['word'])
                    else: frontier_capped += 1
                    continue
                certified += 1; comparisons += check_equivalence(I,6)
                out=separator_decision(I,max_schemas=None,max_states=None,max_transitions=None)
                assert out['status'] in ('YES','NO')
                if out['status']=='YES': assert witness(I,out['word']); yes += 1
                else: no += 1
    return dict(instances=instances,certified=certified,uncertified=unknown,
                word_equivalence_checks=comparisons,exact_yes=yes,exact_no=no,
                additional_frontier_decisions=frontier_extra,
                frontier_unknown_or_capped=frontier_capped)


def encoded_obstruction():
    old=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),
                 frozenset({(0,2),(0,3),(1,2)}))
    encoded=uniform_code(old); summary,cert=separator_certificate(encoded)
    # Helpers 7 and 9 are the second physical zero transitions of the two
    # synchronized logical-zero classes; 9 enters the final and forces both.
    assert cert is not None and cert.marked==frozenset({(7,0),(9,0)})
    compiled=compile_separators(encoded,cert)
    direct=marker_decision(compiled,max_schemas=None,max_states=None,max_transitions=None)
    assert direct['status']=='NO'
    answer=separator_decision(encoded,max_schemas=None,max_states=None,max_transitions=None)
    source=separator_decision(old,max_schemas=None,max_states=None,max_transitions=None)
    assert answer['status']==source['status']=='NO'
    return dict(source_status='NO',encoded_status='NO',marked=summary['marked'],
                compiled_states=len(compiled.delta),equivalence_checks=check_equivalence(encoded,12),
                downstream_schemas=direct['schemas'])


def early_cycle_fixture():
    I=Instance(((1,0),(-1,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    strict,_=separator_certificate(I); assert strict['status']=='NOT_APPLICABLE'
    out=frontier_separator_decision(I,UNCAPPED)
    assert out['status']=='YES' and witness(I,out['word'])
    assert check_equivalence(I,7,frontier=True)>0
    return dict(strict=strict,frontier_status=out['status'],word=out['word'])


def target_cycle_fixture():
    I=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    out=frontier_separator_decision(I,UNCAPPED)
    assert out['status']=='UNKNOWN'
    return dict(status=out['status'],reason=out.get('reason'))


def main():
    result={'status':'PASS','small_census':small_census(),
            'encoded_obstruction':encoded_obstruction(),
            'early_cycle_fixture':early_cycle_fixture(),
            'target_cycle_fixture':target_cycle_fixture(),
            'scope':'Exact on C053/C056 synchronous-separator certified terminal instances only',
            'proof_status':'Written proof + reproducible checks; independent mathematical review pending; not newly Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'synchronous-separators.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

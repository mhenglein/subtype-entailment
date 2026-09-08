"""Independent checks for synchronous-separator preprocessing."""
from itertools import product
import json
from pathlib import Path

from border_lab import Instance, border_witness, witness, words
from marker_certificate import marker_structure
from target_frontier import Limits as FrontierLimits
from synchronous_separators import (compile_separators, encode_word,
    separator_certificate, frontier_separator_certificate,
    frontier_separator_decision)

UNCAPPED = FrontierLimits(states=None, transitions=None, descriptors=None,
                          schemas=None, reconstruction=None)


def uniform_code(I):
    k=len(I.delta); table=[]
    for p in range(k):
        table.append((k+I.delta[p][0] if I.delta[p][0]>=0 else -1,
                      k+I.delta[p][1] if I.delta[p][1]>=0 else -1))
    table.extend((q,-1) for q in range(k))
    return Instance(tuple(table),I.final,I.flags,I.bad,I.start)


def check_equivalence(I,maximum,frontier=False):
    _,cert=(frontier_separator_certificate(I) if frontier else separator_certificate(I))
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
    instances=certified=comparisons=uncertified=frontier_structural=0
    for k in range(1,4):
        possible=[(p,q) for p in range(k-1) for q in range(k-1) if p!=q]
        for raw in product(range(-1,k),repeat=2*(k-1)):
            delta=tuple(tuple(raw[2*p:2*p+2]) for p in range(k-1))+((-1,-1),)
            for mask in range(1<<len(possible)):
                flags=frozenset(pair for i,pair in enumerate(possible) if mask>>i&1)
                I=Instance(delta,frozenset({k-1}),flags); instances += 1
                _,cert=separator_certificate(I)
                if cert is None:
                    uncertified += 1
                    _,front=frontier_separator_certificate(I)
                    if front is not None: frontier_structural += 1
                    continue
                certified += 1; comparisons += check_equivalence(I,6)
    return dict(instances=instances,certified=certified,uncertified=uncertified,
                word_equivalence_checks=comparisons,
                frontier_colourings_on_strict_failures=frontier_structural)


def encoded_obstruction():
    old=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),
                 frozenset({(0,2),(0,3),(1,2)}))
    encoded=uniform_code(old); summary,cert=separator_certificate(encoded)
    assert cert is not None and cert.marked==frozenset({(7,0),(9,0)})
    compiled=compile_separators(encoded,cert)
    structures=[]
    for f in compiled.final:
        structure,_,_=marker_structure(compiled,f,code='paired')
        assert structure['status']=='CERTIFIED'
        structures.append(structure)
    # C053 is already independently reproduced by the consolidated continuation
    # suite. Here we test the new compiler/equivalence and its exact applicability,
    # rather than redundantly rerunning its potentially large schema graph.
    return dict(encoded_known_no=True,marked=summary['marked'],
                compiled_states=len(compiled.delta),equivalence_checks=check_equivalence(encoded,12),
                c053_structures=structures)


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

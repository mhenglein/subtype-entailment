"""Check the unary two-copy arithmetic detectors; not an undecidability test."""
from itertools import product
from pathlib import Path
import json
from trailing_copy_barrier import Edge,Machine,encode,in_regular_candidate,arithmetic_bad,error_patterns

ROOT=Path(__file__).resolve().parents[1]


def check():
    count=valid=bad=0
    # Every update vector, with each selected source value available after a
    # syntactically valid prior step. The first step's arithmetic is irrelevant
    # to the selected-edge detector, so check that separately from the union.
    selected=0
    for changes in product((-1,0,1),repeat=2):
        M=Machine((Edge(0,1,(1,1)),Edge(1,2,changes)),0,frozenset({2}))
        patterns=error_patterns(M)
        for a,b,na,nb in product(range(5),repeat=4):
            configs=[(0,0,0),(1,a,b),(2,na,nb)];ids=[0,1]
            if not in_regular_candidate(M,configs,ids):continue
            w=encode(configs,ids)
            for counter,delta in enumerate(changes):
                expected=(na,nb)[counter]!=(a,b)[counter]+delta
                actual=any(p['regex'].fullmatch(w) for p in patterns if p['edge']==1 and p['counter']==counter)
                assert actual==expected
                selected+=1
            anybad=arithmetic_bad(M,configs,ids)
            assert any(p['regex'].fullmatch(w) for p in patterns)==anybad
            count+=1;bad+=anybad;valid+=not anybad
    # A correct first increment, incorrect INTERNAL update, and correct final
    # update: the witness to the numerical error is not anchored at word end.
    M=Machine((Edge(0,1,(1,0)),Edge(1,2,(1,0)),Edge(2,3,(0,0))),0,frozenset({3}))
    configs=[(0,0,0),(1,1,0),(2,7,0),(3,7,0)]
    ids=[0,1,2];word=encode(configs,ids)
    assert in_regular_candidate(M,configs,ids)
    found=[p for p in error_patterns(M) if p['regex'].fullmatch(word)]
    assert found and all(p['edge']==1 for p in found)
    # Tests restrict the regular language but do not change the copy arithmetic.
    Z=Machine((Edge(0,1,(1,0),(0,0)),Edge(1,2,(-1,1),(1,0))),0,frozenset({2}))
    assert in_regular_candidate(Z,[(0,0,0),(1,1,0),(2,0,1)],[0,1])
    assert not in_regular_candidate(Z,[(0,0,0),(1,0,0),(2,0,1)],[0,1])
    result=dict(status='PASS',candidate_histories=count,valid_numeric_histories=valid,
        erroneous_histories=bad,selected_counter_queries=selected,
        interior_error=dict(word=word,matched_edges=sorted(set(p['edge'] for p in found))),
        proof_status='Written reduction for a nearby trailing-context pattern problem; not a reduction to BorderAvoid',
        original_gap='Remove the arbitrary trailing context without changing the exact terminal comparison semantics')
    (ROOT/'results'/'trailing-copy-barrier.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':check()

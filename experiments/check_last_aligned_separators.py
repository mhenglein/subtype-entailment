"""Discriminating checks for last_aligned_separators."""
import json
from pathlib import Path

from border_lab import Instance, witness, border_witness, words
from last_aligned_separators import (compile_last_aligned,
    last_aligned_certificate,last_aligned_decision)
from macro_marker_spectrum import semantic_macro_decision
from synchronous_separators import (compile_separators,
    frontier_separator_certificate)
from target_frontier import Limits

UNCAPPED=Limits(states=None,transitions=None,descriptors=None,schemas=None,
                reconstruction=None)


def uniform_code(I):
    k=len(I.delta); table=[]
    for p in range(k):
        table.append((k+I.delta[p][0] if I.delta[p][0]>=0 else -1,
                      k+I.delta[p][1] if I.delta[p][1]>=0 else -1))
    table.extend((q,-1) for q in range(k))
    return Instance(tuple(table),I.final,I.flags,I.bad,I.start)


def strict_improvement():
    source=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),
                    frozenset({(0,2),(0,3),(1,2)}))
    encoded=uniform_code(source)
    encoded=Instance(encoded.delta,encoded.final,
                     encoded.flags|frozenset({(6,7)}),encoded.bad,encoded.start)

    # The added helper-state flag is deliberately irrelevant to last-aligned
    # violations: its mandatory 0 step lands in the existing flag (1,2).
    all_summary,all_cert=frontier_separator_certificate(encoded)
    assert all_cert is not None
    all_compiled=compile_separators(encoded,all_cert)
    all_out=semantic_macro_decision(all_compiled,UNCAPPED)

    last_summary,last_compiled=compile_last_aligned(encoded)
    assert last_compiled is not None
    last_out=last_aligned_decision(encoded,UNCAPPED)
    assert last_out['status']=='NO'

    # The new root must not change the productive last-aligned marking relative
    # to the same encoded instance without that root.
    base_summary,_=last_aligned_certificate(uniform_code(source))
    assert last_summary['marked']==base_summary['marked']
    assert all_summary['marked']!=last_summary['marked']
    return dict(all_pair_status=all_out['status'],last_aligned_status='NO',
                all_pair_marked=all_summary['marked'],
                last_aligned_marked=last_summary['marked'],
                live_pair_vertices=last_summary['live_pair_vertices'])


def witness_preservation_sample():
    fixtures=[
      Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)})),
      Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),
               frozenset({(0,2),(0,3),(1,2)})),
      Instance(((1,0),(-1,2),(-1,-1)),frozenset({2}),frozenset({(0,1)})),
    ]
    checks=0
    for I in fixtures:
        summary,J=compile_last_aligned(I)
        assert J is not None,summary
        # Compare exact direct predicates on all defined words through length 8.
        for w in words('01',8):
            if I.run(w) is None: continue
            # Reconstruct the compiled word from the marked transition set.
            run=I.run(w); out=[]; marked={tuple(x) for x in summary['marked']}
            for i,a in enumerate(w):
                out.append('1'+a)
                if (run[i],int(a)) in marked: out.append('00')
            ew=''.join(out)
            assert witness(I,w)==witness(J,ew)
            assert border_witness(I,w)==border_witness(J,ew)
            checks+=1
    return checks


def main():
    result={'status':'PASS','strict_improvement':strict_improvement(),
            'witness_preservation_checks':witness_preservation_sample(),
            'scope':'Boundary-normalized binary single-final terminal slices; finite compiled macro spectrum is exact',
            'proof_status':'Written proof inherited/implemented from synchronized-tail note; independent review pending; not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'last-aligned-separators.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()

"""Reproducible continuation of A008/A009; no claims from capped searches."""
from border_lab import Instance, Sandwich, witness, border_witness, sufficient, word_budget
from dataclasses import replace
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
BASE=Instance(((3,-1),(0,2),(1,4),(5,3),(1,2),(5,4)),frozenset({2,5}),frozenset({(0,5),(3,4),(4,1),(5,4)}))

def encode(I):
    return dict(delta=I.delta,final=sorted(I.final),flags=sorted(I.flags),bad=sorted(I.bad),start=I.start,alphabet=I.alphabet)

def budgets(I, maximum=8, cap=200000):
    rows=[]
    for B in range(maximum+1):
        for L in range(B+1):
            D=B-L
            r=Sandwich(I,L,D,True).search(cap)
            rows.append(dict(L=L,D=D,**r))
            if r['status']=='YES':
                w=r['word']
                assert witness(I,w) and border_witness(I,w) and sufficient(I,w,L,D)
                status='EXACT' if all(x['status']=='NO' for x in rows[:-1]) else 'UPPER_BOUND'
                return dict(status=status,budget=B,word=w,word_budget=word_budget(I,w),searches=rows)
    return dict(status='NO_THROUGH' if all(x['status']=='NO' for x in rows) else 'UNKNOWN',through=maximum,searches=rows)

if __name__=='__main__':
    out=budgets(BASE,5)
    assert out['status']=='EXACT' and out['budget']==5
    print('Baseline',out['status'],out['budget'],out['word'],BASE.run(out['word']))
    (ROOT/'results/baseline-replay.json').write_text(json.dumps(dict(instance=encode(BASE),result=out),indent=2)+'\n')
    for pair in sorted(BASE.flags):
        I=replace(BASE,flags=BASE.flags-{pair})
        r=budgets(I,5)
        print('Remove flag',pair,r['status'],r.get('budget'),r.get('word'))

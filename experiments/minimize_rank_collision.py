from prefix_rank_layers import *
from pathlib import Path
import json
root=Path(__file__).resolve().parents[1]
a=json.loads((root/'results/rich-rank-collision.json').read_text())
I=Instance(tuple(map(tuple,a['delta'])),frozenset({a['k']-1}),frozenset(map(tuple,a['flags'])))
checks=0

def collision(I):
    global checks
    checks+=1
    h=enriched_heuristic(I,'rich',max_calls=3000,max_states=10000)
    if h['status']!='EXHAUSTED_HEURISTIC':return False
    w=bounded_witness(I,14,50000)
    return w if w['status']=='FOUND_WITNESS' else False

def trim(I):
    reach={I.start}; todo=list(reach)
    for q in todo:
        for p in I.delta[q]:
            if p>=0 and p not in reach:reach.add(p);todo.append(p)
    rev={q:[] for q in range(len(I.delta))}
    for q,row in enumerate(I.delta):
        for p in row:
            if p>=0:rev[p].append(q)
    live=set(I.final);todo=list(live)
    for q in todo:
        for p in rev[q]:
            if p not in live:live.add(p);todo.append(p)
    live &=reach
    if I.start not in live:return I
    ids={q:i for i,q in enumerate(sorted(live))}
    return Instance(tuple(tuple(ids.get(t,-1) for t in I.delta[q]) for q in sorted(live)),
                    frozenset(ids[q] for q in I.final if q in ids),
                    frozenset((ids[p],ids[q]) for p,q in I.flags if p in ids and q in ids),
                    start=ids[I.start])
change=True
while change:
    change=False
    for e in sorted(I.flags):
        J=Instance(I.delta,I.final,I.flags-{e},start=I.start)
        if collision(J):I=J;change=True;break
    if change:continue
    for p,row in enumerate(I.delta):
        for a,t in enumerate(row):
            if t<0:continue
            d=list(map(list,I.delta));d[p][a]=-1
            J=Instance(tuple(map(tuple,d)),I.final,I.flags,start=I.start)
            if collision(J):I=J;change=True;break
        if change:break
    J=trim(I)
    if J!=I and collision(J):I=J;change=True
out=dict(delta=I.delta,final=sorted(I.final),flags=sorted(I.flags),start=I.start,
         known=collision(I),rich=enriched_heuristic(I,'rich'),minimization_checks=checks)
(root/'results/minimized-rich-rank-collision.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

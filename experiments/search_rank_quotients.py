from prefix_rank_layers import *
import random,json,time,sys
from pathlib import Path
root=Path(__file__).resolve().parents[1]
rng=random.Random(2026091518)
counts={};beg=time.time()
for trial in range(30000):
    k=rng.randrange(3,10)
    D=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k-1))+((-1,-1),)
    rate=rng.choice((.10,.20,.35,.5))
    G=frozenset((p,q) for p in range(k-1) for q in range(k-1) if p!=q and rng.random()<rate)
    I=Instance(D,frozenset({k-1}),G)
    simple=shortest_endpoint_heuristic(I,max_calls=1000,max_states=3000)
    if simple['status']=='FOUND_WITNESS':
        counts['simple_found']=counts.get('simple_found',0)+1;continue
    H=enriched_heuristic(I,'action',max_calls=1000,max_states=5000)
    counts[H['status']]=counts.get(H['status'],0)+1
    if H['status']=='EXHAUSTED_HEURISTIC':
        W=bounded_witness(I,14,30000)
        if W['status']=='FOUND_WITNESS':
            out=dict(trial=trial,k=k,delta=D,flags=sorted(G),known=W,heuristic=H,seed=2026091518)
            path=root/'results'/'action-rank-collision.json';path.write_text(json.dumps(out,indent=2)+'\n')
            print('ACTION COLLISION',json.dumps(out),flush=True)
            rich=enriched_heuristic(I,'rich',max_calls=2000,max_states=10000)
            print('RICH',rich,flush=True)
            if rich['status']=='EXHAUSTED_HEURISTIC':
                out['rich']=rich
                (root/'results'/'rich-rank-collision.json').write_text(json.dumps(out,indent=2)+'\n')
                break
    if trial%1000==0: print(trial,counts,round(time.time()-beg,1),flush=True)
else:print('no full collision',counts,flush=True)

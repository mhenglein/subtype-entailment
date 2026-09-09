"""Exploratory exact finite-order oracle for homogeneous stage chains."""
from itertools import product
import json, random, time
from pathlib import Path
from border_lab import Instance, witness
from power_transport import saturate


def stage_chain(r,flags):
    rows=[]
    for i in range(r):rows.extend(((2*i+1,-1),(2*i+1,2*i+2)))
    rows.append((-1,-1))
    return Instance(tuple(rows),frozenset({2*r}),frozenset(flags))


def weak_orders(r):
    # Every order/equality pattern has one consecutive-rank representative.
    return [v for v in product(range(1,r+1),repeat=r) if set(v)==set(range(1,max(v)+1))]


def profile_flags(lengths,flaglist):
    r=len(lengths);hits=set()
    for i in range(r):
        for j in range(i+1,r):
            if any(lengths[i+h]!=lengths[j+h] for h in range(1,r-j)):continue
            a,b=lengths[i],lengths[j]
            hits.add((2*i+1,2*j+1))
            if a==b:hits.add((2*i,2*j))
            elif a<b:hits.add((2*i,2*j+1))
            else:hits.add((2*i+1,2*j))
    return sum(1<<j for j,p in enumerate(flaglist) if p in hits)


def test(r=3,cap=None):
    pairs=[(2*i+a,2*j+b) for i in range(r) for j in range(i+1,r) for a in range(2) for b in range(2)]
    orders=weak_orders(r);profiles=[profile_flags(v,pairs) for v in orders]
    masks=range(1<<len(pairs)) if cap is None else [random.Random(i+2026090868).randrange(1<<len(pairs)) for i in range(cap)]
    yes=no=closed=0;misses=[];start=time.time()
    for mask in masks:
        if any(not mask&p for p in profiles):yes+=1;continue
        no+=1;I=stage_chain(r,[p for i,p in enumerate(pairs) if mask>>i&1])
        result,J=saturate(I,max_states=100000)
        # Every stage state is visited on every candidate, so any final-column
        # flag certifies that the entire candidate language is eliminated.
        if any(q==2*r for p,q in J.flags):closed+=1
        else:
            misses.append(dict(flags=sorted(I.flags),result=result))
            if len(misses)>=10:break
    return dict(r=r,yes=yes,no=no,closed=closed,misses=misses,seconds=time.time()-start)

if __name__=='__main__':
    import sys
    r=int(sys.argv[1]) if len(sys.argv)>1 else 3
    cap=int(sys.argv[2]) if len(sys.argv)>2 else None
    result=test(r,cap)
    path=Path(__file__).resolve().parents[1]/'results'/('calculus-stage-search-'+str(r)+'.json')
    path.parent.mkdir(exist_ok=True)
    saved={k:v for k,v in result.items() if k!='seconds'}
    path.write_text(json.dumps(saved,indent=2)+'\n')
    print({k:v if k!='misses' else len(v) for k,v in result.items()})
    for m in result['misses'][:3]:print('MISS',m['flags'])

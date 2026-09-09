"""A limit of finite flag saturation, not of the existing short-test method.

The candidate graph is the one-flag four-state example restricted by a regular
history bit: a zero must have occurred from the original state zero. This makes
every candidate bad with minimum proper violation one. The new annotation
calculus still has unbounded last-aligned lengths at its fixed point.
"""
from border_lab import Instance


def short_detectable_limit():
    D=((0,2),(3,0),(1,1),(-1,-1))
    # Restrict candidates to those with a zero edge out of state zero.
    states=[(0,False)];ix={states[0]:0};rows=[]
    for p,seen in states:
        row=[]
        for a,q in enumerate(D[p]):
            if q<0:row.append(-1);continue
            t=(q,seen or (p==0 and a==0))
            if t not in ix:ix[t]=len(states);states.append(t)
            row.append(ix[t])
        rows.append(tuple(row))
    F={ix[p,b] for p,b in states if p==3 and b}
    G={(i,j) for i,(p,s) in enumerate(states) for j,(q,t) in enumerate(states) if p==0 and q==1}
    I=Instance(tuple(rows),frozenset(F),frozenset(G))
    # Trim to reachable/co-reachable states, preserving initial ordering.
    live=set(F)
    while True:
        old=set(live)
        live|={p for p,row in enumerate(rows) if any(q in live for q in row)}
        if live==old:break
    keep=sorted(live);m={p:i for i,p in enumerate(keep)}
    return Instance(tuple(tuple(m.get(q,-1) for q in rows[p]) for p in keep),
                    frozenset(m[q] for q in F),frozenset((m[p],m[q]) for p,q in G if p in m and q in m)),[states[p] for p in keep]

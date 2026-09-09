"""Cross-gap periodic-grid implication plus guarded backward saturation.

Unlike gap_equivalence, this rule can discharge a comparison by a G violation
at an INTEGER MULTIPLE of its gap. Failed certification is not witnesshood.
Every successful rule preserves the complete witness language when its new
flag is added. No completeness claim for the combined calculus is made.
"""
from collections import deque
from border_lab import Instance
from collective_transport import validate
from collective_transport import backward_closure
from gap_equivalence import _safe, _flags, _heads, _cap, ResourceLimit, bad_gaps


def _reach(I):
    out=[]
    for p in range(len(I.delta)):
        seen=set();todo=[q for q in I.delta[p] if q>=0]
        for q in todo:
            if q in seen:continue
            seen.add(q);todo.extend(r for r in I.delta[q] if r>=0 and r not in seen)
        out.append(seen)
    return out


def _tuples(I,p,q,size,reach):
    if size<2 or q not in reach[p]:return
    todo=[(p,q)]
    while todo:
        at=todo.pop()
        if len(at)==size:
            yield at;continue
        if at[-1] in I.final:continue
        for r in reversed(sorted(reach[at[-1]]-set(at))):
            todo.append(at+(r,))


def periodic_grid(I,w,start,gap):
    """Literal positive-grid agreements on one word, including empty tails."""
    c=I.run(w);n=len(w)
    return [(i,j,c[i],c[j]) for i in range(start,n+1) for j in range(i+gap,n+1,gap)
            if w[i:].startswith(w[j:])]


def harmonic_implication(I,pair,G=None,max_states=200000):
    """Every occurrence of pair entails G somewhere on its periodic grid.

    CERTIFIED is all-length. NOT_CERTIFIED returns an actual pair comparison
    with no G comparison on that grid; it can still have G at other gaps.
    UNKNOWN means the finite orbit search was capped.
    """
    validate(I);G=_flags(I,I.flags if G is None else G);pair=tuple(pair)
    if len(pair)!=2 or any(type(q) is not int or not 0<=q<len(I.delta) for q in pair):
        raise ValueError('Invalid pair')
    if max_states is not None and (type(max_states) is not int or max_states<1):
        raise ValueError('max_states must be positive or None')
    if pair in G:return dict(status='CERTIFIED',reason='already flagged',states=0,tuples=0)
    p,q=pair
    if p==q:return dict(status='NOT_SUPPORTED',reason='diagonal antecedent')
    J=_safe(I)
    if J is None or p in I.final:return dict(status='CERTIFIED',reason='no admissible occurrence',states=0,tuples=0)
    heads=_heads(J);head=next((w for (r,a),w in heads.items() if r==p),None)
    if head is None:return dict(status='CERTIFIED',reason='unreachable source',states=0,tuples=0)
    reach=_reach(J);k=len(I.delta);states=nt=0
    def good(coords):
        return len(set(coords))==len(coords) and not any((x,y) in G
                          for i,x in enumerate(coords) for y in coords[i+1:])
    try:
        for e in range(1,k):
            for Q in _tuples(J,p,q,e+1,reach):
                if any(x in J.final for x in Q[:-1]) or not good(Q):continue
                nt+=1
                first=('u',Q,False)
                parent={first:None};todo=deque([first]);states+=1
                _cap(states,max_states,'periodic-grid state cap')
                while todo:
                    phase,coords,used=state=todo.popleft()
                    if phase=='v' and used and coords==Q[1:]:
                        parts={'u':[],'v':[]};at=state
                        while parent[at] is not None:
                            prev,a=parent[at]
                            if a is not None:parts[prev[0]].append(a)
                            at=prev
                        u=''.join(reversed(parts['u']));v=''.join(reversed(parts['v']))
                        w=head+(u+v)*e+u;d=len(u)+len(v);i=len(head);j=i+d
                        c=I.run(w)
                        assert I.admissible(w) and (c[i],c[j])==pair and w[i:].startswith(w[j:])
                        grid=periodic_grid(I,w,i,d)
                        assert not any((r,s) in G for x,y,r,s in grid)
                        return dict(status='NOT_CERTIFIED',word=w,i=i,j=j,gap=d,
                                    u=u,v=v,exponent=e,states=states,tuples=nt,
                                    actual_G_gaps=sorted(bad_gaps(I,w,G)))
                    succ=[]
                    if phase=='u' and coords[-1] in J.final:
                        succ.append((('v',coords[:-1],False),None))
                    else:
                        for a in range(2):
                            nc=tuple(J.delta[r][a] for r in coords)
                            if min(nc)>=0 and good(nc):succ.append(((phase,nc,phase=='v'),str(a)))
                    for nxt,a in succ:
                        if nxt not in parent:
                            states+=1;_cap(states,max_states,'periodic-grid state cap')
                            parent[nxt]=(state,a);todo.append(nxt)
        return dict(status='CERTIFIED',states=states,tuples=nt)
    except ResourceLimit as error:
        return dict(status='UNKNOWN',reason=str(error),states=states,tuples=nt)


def saturate(I,max_states=200000):
    """Finite sound annotation calculus. A capped rule is never added.

    Each productive round adds at least one flag; at most k^2 rounds can add
    anything. This termination concerns normalization, not witness existence.
    """
    validate(I);J=I;history=[];uncertain=False
    while True:
        B,rules=backward_closure(J)
        if B!=J.flags:
            additions=sorted(B-J.flags)
            history.append(dict(rule='backward',added=additions,
                                premises=[dict(pair=list(v),predecessors=sorted(ps))
                                          for v,ps in sorted(rules.items())]))
            J=Instance(J.delta,J.final,B,J.bad,J.start,J.alphabet)
        change=False
        for p in range(len(I.delta)):
            for q in range(len(I.delta)):
                if p==q or (p,q) in J.flags or p in I.final:continue
                answer=harmonic_implication(J,(p,q),max_states=max_states)
                if answer['status']=='CERTIFIED':
                    history.append(dict(rule='periodic_grid',added=[[p,q]],certificate=answer))
                    J=Instance(J.delta,J.final,J.flags|{(p,q)},J.bad,J.start,J.alphabet)
                    change=True
                elif answer['status']=='UNKNOWN':uncertain=True
        if not change:break
    return dict(status='PARTIAL' if uncertain else 'SATURATED_IN_CALCULUS',
                flags=sorted(J.flags),added=sorted(J.flags-I.flags),steps=history),J


if __name__=='__main__':
    import time
    from gap_equivalence import equality_cycle
    from lastflag_spectrum import decide
    I=equality_cycle();t=time.time()
    print(harmonic_implication(I,(0,2),max_states=None))
    result,J=saturate(I,max_states=None)
    print('elapsed',time.time()-t,'status',result['status'],'flags',result['flags'])
    print('decision',decide(J))

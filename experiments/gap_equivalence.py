"""Decide flag implication/equivalence separately at every positive gap.

The target is *not* unrestricted witness existence. A separating word may be
bad under both annotations, but at different gaps. The uncapped algorithm is
finite and exact on terminal partial binary automata. Written proof accompanies
this module; this is not a Lean-verified implementation.
"""
from collections import deque
from dataclasses import dataclass
from typing import Optional

from border_lab import Instance
from collective_transport import validate


@dataclass(frozen=True)
class Limits:
    actions: Optional[int] = 20000
    checks: Optional[int] = 2000000

    def __post_init__(self):
        for name, value in self.__dict__.items():
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError(name + ' must be positive or None')


class ResourceLimit(RuntimeError):
    pass


def _cap(value, cap, reason):
    if cap is not None and value > cap:
        raise ResourceLimit(reason)


def _flags(I, flags):
    out = frozenset(tuple(p) for p in flags)
    if any(len(p) != 2 or any(type(q) is not int or not 0 <= q < len(I.delta)
                            for q in p) for p in out):
        raise ValueError('Invalid flag relation')
    return out


def bad_gaps(I, word, flags=None):
    """Direct reference definition. Gap zero is kept for diagonal comparisons."""
    if not I.admissible(word):
        return frozenset()
    c = I.run(word)
    G = I.flags if flags is None else flags
    return frozenset(j-i for i in range(len(word)+1) for j in range(i,len(word)+1)
                     if (c[i],c[j]) in G and word[i:].startswith(word[j:]))


def _safe(I):
    if I.start in I.bad:
        return None
    table = tuple(tuple(q if p not in I.bad and q not in I.bad else -1 for q in row)
                  for p,row in enumerate(I.delta))
    # Do not normalize G/H boundary flags: their *positive-gap* differences
    # are part of the problem being decided, not removable inadmissibility.
    return Instance(table,I.final,I.flags,frozenset(),I.start,I.alphabet)


def _heads(I):
    """Shortest safe prefixes by endpoint and last symbol; None means empty."""
    first=(I.start,None)
    words={first:''}; todo=deque([first])
    while todo:
        p,last=todo.popleft()
        for a,q in enumerate(I.delta[p]):
            nxt=(q,a)
            if q>=0 and nxt not in words:
                words[nxt]=words[p,last]+str(a)
                todo.append(nxt)
    return words


def _diagonal_difference(I,G,H):
    g={p for p,q in G if p==q}
    h={p for p,q in H if p==q}
    if not g-h or I.start in h:
        return None
    first=(I.start,I.start in g)
    parent={first:None};todo=deque([first])
    while todo:
        p,hit=at=todo.popleft()
        if p in I.final and hit:
            letters=[]
            while parent[at] is not None:
                at,a=parent[at];letters.append(a)
            return ''.join(reversed(letters))
        for a,q in enumerate(I.delta[p]):
            nxt=(q,hit or q in g)
            if q>=0 and q not in h and nxt not in parent:
                parent[nxt]=(at,str(a));todo.append(nxt)
    return None


def _joint(I,G,H):
    """One common-word action: single states, pair hit/avoid monitor, last bit."""
    k=len(I.delta)
    pairs=[(p,q,hit) for p in range(k) if p not in I.final
           for q in range(k) if p!=q for hit in (False,True)]
    ids={p:k+i for i,p in enumerate(pairs)}
    sink=k+len(pairs)
    last0,last1=sink+1,sink+2
    generators=[]
    for a in range(2):
        action=[q if q>=0 else sink for q in (row[a] for row in I.delta)]
        for p,q,hit in pairs:
            r,s=I.delta[p][a],I.delta[q][a]
            pair=(r,s)
            dest=(r,s,hit or pair in G)
            action.append(ids.get(dest,sink) if pair not in H else sink)
        action.extend((sink,last0+a,last0+a))
        generators.append(tuple(action))
    return generators,ids,{i:p for p,i in ids.items()},sink,(last0,last1)


def _monoid(generators,limits):
    identity=tuple(range(len(generators[0])))
    actions=[identity];where={identity:0};reps=[''];at=0
    while at<len(actions):
        for a,g in enumerate(generators):
            effect=tuple(g[q] for q in actions[at])
            if effect not in where:
                _cap(len(actions)+1,limits.actions,'joint action cap')
                where[effect]=len(actions);actions.append(effect)
                reps.append(reps[at]+str(a))
        at+=1
    # The added last-bit machine ensures the identity has no nonempty word.
    return actions,reps


def implication(I,G,H,limits=Limits()):
    """Decide forall accepted w,d: bad_G(w,d) => bad_H(w,d).

    IMPLIES is exhaustive. COUNTEREXAMPLE includes one fully checked word and
    its separating gap. UNKNOWN means a finite computation hit a supplied cap.
    Includes diagonal d=0 and empty target suffixes for positive d.
    """
    validate(I);G=_flags(I,G);H=_flags(I,H)
    if G<=H:
        return dict(status='IMPLIES',reason='flag inclusion',actions=0,checks=0)
    J=_safe(I)
    if J is None:
        return dict(status='IMPLIES',reason='no admissible start',actions=0,checks=0)
    diagonal=_diagonal_difference(J,G,H)
    if diagonal is not None:
        assert 0 in bad_gaps(I,diagonal,G) and 0 not in bad_gaps(I,diagonal,H)
        return dict(status='COUNTEREXAMPLE',word=diagonal,gap=0,actions=0,checks=0)
    G=frozenset((p,q) for p,q in G if p!=q and p not in I.final)
    H=frozenset((p,q) for p,q in H if p!=q and p not in I.final)
    if G<=H:
        return dict(status='IMPLIES',reason='proper flag inclusion',actions=0,checks=0)
    heads=_heads(J)
    if not any(p in J.final for p,a in heads):
        return dict(status='IMPLIES',reason='empty candidate language',actions=0,checks=0)
    checks=0;count=0
    try:
        generators,ids,pairof,sink,lastbits=_joint(J,G,H)
        actions,reps=_monoid(generators,limits);count=len(actions)
        # p is the start of the LONGEST d-periodic suffix. A nonempty head
        # must end in the opposite letter to v, or the pair monitor would
        # miss an earlier matching comparison with the same gap.
        for bi,B in enumerate(actions):
            if not reps[bi]:
                continue
            b=B[lastbits[0]]-lastbits[0]
            assert b in (0,1) and reps[bi][-1]==str(b)
            choices={p:x for (p,a),x in heads.items() if a is None or a!=b}
            for ai,A in enumerate(actions):
                for p,x in sorted(choices.items()):
                    if p in J.final:continue
                    checks+=1;_cap(checks,limits.checks,'action combination cap')
                    q=B[A[p]]
                    if q>=len(J.delta) or p==q or (p,q) in H:
                        continue
                    pair=ids[p,q,(p,q) in G]
                    for e in range(1,len(J.delta)):
                        end=A[pair]
                        if end in pairof:
                            r,s,hit=pairof[end]
                            if s in J.final and hit:
                                u,v=reps[ai],reps[bi]
                                word=x+(u+v)*e+u;gap=len(u)+len(v)
                                assert gap in bad_gaps(I,word,G)
                                assert gap not in bad_gaps(I,word,H)
                                return dict(status='COUNTEREXAMPLE',word=word,gap=gap,
                                            head=x,u=u,v=v,exponent=e,actions=count,checks=checks)
                        pair=B[A[pair]]
                        if pair==sink:break
        return dict(status='IMPLIES',actions=count,checks=checks)
    except ResourceLimit as error:
        return dict(status='UNKNOWN',reason=str(error),actions=count,checks=checks)


def equivalent(I,G,H,limits=Limits()):
    forward=implication(I,G,H,limits)
    if forward['status']=='COUNTEREXAMPLE':
        return dict(status='DIFFERENT_GAPS',direction='G_not_H',check=forward)
    backward=implication(I,H,G,limits)
    if backward['status']=='COUNTEREXAMPLE':
        return dict(status='DIFFERENT_GAPS',direction='H_not_G',check=backward)
    status='EQUIVALENT_GAPS' if forward['status']==backward['status']=='IMPLIES' else 'UNKNOWN'
    return dict(status=status,forward=forward,backward=backward)


def saturate(I,limits=Limits()):
    """Unique greatest annotation preserving the bad-gap relation, or partial.

    Every added pair has its own exact implication certificate. Exhaustive
    absence of candidates establishes maximality *on this fixed automaton*.
    This does not purport to classify arbitrary witness-language equivalences.
    """
    validate(I)
    flags=set(I.flags);unknown=False;records=[]
    for p in range(len(I.delta)):
        for q in range(len(I.delta)):
            if (p,q) in flags:continue
            check=implication(I,{(p,q)},I.flags,limits)
            if check['status']=='IMPLIES':flags.add((p,q))
            elif check['status']=='UNKNOWN':unknown=True
            records.append(dict(pair=[p,q],**check))
    # Proof by union: each new flag independently implies the old bad gap.
    J=Instance(I.delta,I.final,frozenset(flags),I.bad,I.start,I.alphabet)
    return dict(status='PARTIAL' if unknown else 'MAXIMAL_GAP_EQUIVALENT',
                flags=sorted(flags),added=sorted(flags-I.flags),checks=records),J


def equality_cycle():
    """Seven-state NO: m=l, then n=m, but n=l is forbidden.

    Candidates 0^n1 0^m1 0^l1, all exponents positive. The contradiction involves
    DIFFERENT comparison gaps. It will be used to test the limits of saturation.
    """
    return Instance(((1,-1),(1,2),(3,-1),(3,4),(5,-1),(5,6),(-1,-1)),
                    frozenset({6}),frozenset({(2,5),(3,4),(0,3),(1,2),(0,4)}))



def orbit_implication(I,G,H,max_states=200000):
    """Independent exact backend: enumerate injective periodic-orbit tuples.

    It reads one common u then one common v across all copies, rather than
    enumerating transition functions. Only adjacent orbit coordinates are
    checked: they represent precisely ONE comparison gap.
    """
    from itertools import permutations
    validate(I);G=_flags(I,G);H=_flags(I,H)
    if max_states is not None and (type(max_states) is not int or max_states<1):
        raise ValueError('max_states must be positive or None')
    if G<=H:return dict(status='IMPLIES',states=0,tuples=0)
    J=_safe(I)
    if J is None:return dict(status='IMPLIES',states=0,tuples=0)
    diag=_diagonal_difference(J,G,H)
    if diag is not None:return dict(status='COUNTEREXAMPLE',word=diag,gap=0,states=0,tuples=0)
    G=frozenset((p,q) for p,q in G if p!=q and p not in I.final)
    H=frozenset((p,q) for p,q in H if p!=q and p not in I.final)
    if G<=H:return dict(status='IMPLIES',states=0,tuples=0)
    heads=_heads(J);k=len(J.delta);total=0;nt=0
    def observe(coords,hit):
        if len(set(coords))!=len(coords):return None
        for p,q in zip(coords,coords[1:]):
            if (p,q) in H:return None
            hit |= (p,q) in G
        return hit
    try:
        for e in range(1,k):
            for Q in permutations(range(k),e+1):
                if any(p in J.final for p in Q[:-1]) or not any(p==Q[0] for p,a in heads):continue
                hit=observe(Q,False)
                if hit is None:continue
                nt+=1
                first=('u',Q,hit,False,-1)
                parent={first:None};todo=deque([first]);total+=1
                _cap(total,max_states,'orbit state cap')
                while todo:
                    state=todo.popleft();phase,coords,hit,used,last=state
                    if phase=='v' and used and hit and coords==Q[1:]:
                        x=heads.get((Q[0],None),heads.get((Q[0],1-last)))
                        if x is not None:
                            parts={'u':[],'v':[]};at=state
                            while parent[at] is not None:
                                prev,letter=parent[at]
                                if letter is not None:parts[prev[0]].append(letter)
                                at=prev
                            u=''.join(reversed(parts['u']));v=''.join(reversed(parts['v']))
                            w=x+(u+v)*e+u;d=len(u)+len(v)
                            assert d in bad_gaps(I,w,G) and d not in bad_gaps(I,w,H)
                            return dict(status='COUNTEREXAMPLE',word=w,gap=d,
                                        head=x,u=u,v=v,exponent=e,states=total,tuples=nt)
                    successors=[]
                    if phase=='u' and coords[-1] in J.final:
                        successors.append((('v',coords[:-1],hit,False,-1),None))
                    else:
                        for a in range(2):
                            dest=tuple(J.delta[p][a] for p in coords)
                            if min(dest)<0:continue
                            h=observe(dest,hit)
                            if h is None:continue
                            successors.append(((phase,dest,h,phase=='v',a if phase=='v' else -1),str(a)))
                    for nxt,letter in successors:
                        if nxt not in parent:
                            total+=1;_cap(total,max_states,'orbit state cap')
                            parent[nxt]=(state,letter);todo.append(nxt)
        return dict(status='IMPLIES',states=total,tuples=nt)
    except ResourceLimit as error:
        return dict(status='UNKNOWN',reason=str(error),states=total,tuples=nt)


if __name__=='__main__':
    from collective_transport import barrier,transported_barrier
    I=barrier();J=transported_barrier()
    print(equivalent(I,I.flags,J.flags))
    result,S=saturate(I)
    print(result['status'], result['added'])

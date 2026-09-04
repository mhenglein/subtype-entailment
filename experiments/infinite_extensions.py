"""Exact decision for witnesses admitting an infinite safe continuation.

A NO_INFINITE_EXTENSION result does NOT decide unrestricted entailment.
The finite-terminal remainder is deliberately exposed, not assumed away.
"""
from collections import deque
from safe_extensions import (absorption_holds,zero_region,safe_states,shortest_paths,
                             branching_certificate,primitive,active_rays,advance)
from border_lab import witness,border_witness


def maximal_tails(I,q):
    """Finite terminal paths and simple lassos, in the no-cyclic-branching case."""
    safe=safe_states(I)&zero_region(I)
    if q not in safe: raise ValueError('Safe zero-region state required')
    finite=[]; lassos=[]; todo=[(q,'',(q,))]
    while todo:
        current,word,states=todo.pop()
        outgoing=[(a,r) for a,r in zip(I.alphabet,I.delta[current]) if r in safe]
        if not outgoing: finite.append(word); continue
        for a,r in outgoing:
            nxt=word+a
            if r in states:
                at=states.index(r); lassos.append((nxt[:at],nxt[at:]))
            else: todo.append((r,nxt,states+(r,)))
    return tuple(sorted(set(finite))),tuple(sorted(set(lassos)))


def pure_period(stem,cycle):
    """Canonical phase word if stem cycle^omega is pure periodic; else None."""
    p=primitive(cycle); d=len(p); offset=(-len(stem))%d
    phase=p[offset:]+p[:offset]
    if all(a==phase[i%d] for i,a in enumerate(stem)): return phase
    return None


def monitor_start(I,d):
    buckets=[frozenset() for _ in range(d)]; buckets[0]=frozenset({I.start})
    return I.start,0,tuple(buckets),False


def monitor_step(I,p,offset,state,letter):
    """Remember ordered flags only inside the current p-periodic suffix."""
    q,phase,buckets,conflict=state; d=len(p)
    r=I.delta[q][I.alphabet.index(letter)]
    if r not in safe_states(I): return None
    next_phase=(phase+1)%d
    if letter!=p[(phase-offset)%d]:
        new=[frozenset() for _ in range(d)]; conflict=False
    else:
        new=list(buckets)
        conflict=conflict or any((old,r) in I.flags for old in buckets[next_phase])
    new[next_phase]=new[next_phase]|{r}
    return r,next_phase,tuple(new),conflict


def periodic_prefix_search(I,target,p,max_states=200000):
    """Decide existence of a safe prefix ending at target with viable p^omega."""
    if I.start not in safe_states(I): return dict(status='NO_PREFIX',states=0)
    p=primitive(p); d=len(p); total=0; unknown=False
    for offset in range(d):
        first=monitor_start(I,d); parent={first:None}; todo=deque([first]); capped=False
        while todo:
            state=todo.popleft(); q,phase,_,conflict=state
            if q==target and phase==offset and not conflict:
                letters=[]; node=state
                while parent[node] is not None:
                    node,a=parent[node]; letters.append(a)
                word=''.join(reversed(letters))
                assert p not in active_rays(I,word)
                return dict(status='YES',prefix=word,period=p,states=total+len(parent))
            for a in I.alphabet:
                nxt=monitor_step(I,p,offset,state,a)
                if nxt is not None and nxt not in parent:
                    if len(parent)>=max_states:
                        capped=True; unknown=True; break
                    parent[nxt]=(state,a); todo.append(nxt)
            if capped: break
        total+=len(parent)
    return dict(status='UNKNOWN' if unknown else 'NO_PREFIX',states=total)


def extend_along_lasso(I,prefix,stem,cycle):
    """Construct a finite witness when the lasso differs from every active ray."""
    rays=active_rays(I,prefix); word=prefix; q=I.run(prefix)[-1]; safe=safe_states(I)
    for a in stem:
        if not rays: break
        q=I.delta[q][I.alphabet.index(a)]; assert q in safe
        word+=a; rays=advance(rays,a)
    if rays and len(word)<len(prefix)+len(stem): raise AssertionError('Incomplete stem')
    phase=0; seen=set()
    while rays:
        key=(rays,phase)
        if key in seen: raise ValueError('The lasso is one of the remaining forbidden rays')
        seen.add(key); a=cycle[phase]; phase=(phase+1)%len(cycle)
        q=I.delta[q][I.alphabet.index(a)]; assert q in safe
        word+=a; rays=advance(rays,a)
    assert witness(I,word) and border_witness(I,word)
    return word


def infinite_extension_decision(I,max_states=200000):
    """Exact on absorbing instances absent a resource cap.

    YES provides a finite witness with an infinite safe continuation.
    NO_INFINITE_EXTENSION excludes only that category of witnesses.
    """
    if not absorption_holds(I): return dict(status='UNKNOWN',reason='absorption hypothesis fails')
    safe=safe_states(I); paths=shortest_paths(I,I.start,safe)
    # A branching cycle with an exit guarantees a finite witness, but that
    # particular witness could be terminal. Only use branches whose chosen
    # exit can themselves return to a cycle when certifying this narrower task.
    from safe_extensions import components
    graph=safe&zero_region(I); comps=components(I,graph)
    recurrent=set()
    for group in comps:
        if len(group)>1 or any(q in I.delta[q] for q in group): recurrent.update(group)
    can_infinite=set(recurrent); todo=list(recurrent); reverse={q:set() for q in graph}
    for q in graph:
        for r in I.delta[q]:
            if r in graph: reverse[r].add(q)
    for q in todo:
        for r in reverse[q]:
            if r not in can_infinite: can_infinite.add(r); todo.append(r)
    # Restrict the continuation region to nodes with infinite safe futures.
    # Keep pre-zero paths untouched, but make other zero successors undefined.
    from dataclasses import replace
    delta=tuple(tuple(-1 if q in graph and r not in can_infinite else r for r in row)
                for q,row in enumerate(I.delta))
    J=replace(I,delta=delta)
    branch=branching_certificate(J)
    if branch['status']=='YES' and J.run(branch['word'])[-1] in can_infinite:
        assert witness(I,branch['word'])
        return dict(status='YES',word=branch['word'],method='infinite cyclic branching',certificate=branch)
    rows=[]; unknown=False
    for target in sorted(set(paths)&can_infinite):
        _,lassos=maximal_tails(J,target)
        for stem,cycle in lassos:
            p=pure_period(stem,cycle)
            if p is None:
                word=extend_along_lasso(I,paths[target],stem,cycle)
                return dict(status='YES',word=word,method='nonpure ultimately periodic tail',
                            prefix=paths[target],stem=stem,cycle=cycle)
            answer=periodic_prefix_search(I,target,p,max_states)
            rows.append(dict(target=target,**dict({'period':p},**answer)))
            if answer['status']=='YES':
                word=extend_along_lasso(I,answer['prefix'],'',p)
                return dict(status='YES',word=word,method='finite periodic suffix monitor',
                            certificate=answer,target=target)
            if answer['status']=='UNKNOWN': unknown=True
    return dict(status='UNKNOWN' if unknown else 'NO_INFINITE_EXTENSION',checks=rows,
                scope='does not exclude witnesses with only finite safe continuations')

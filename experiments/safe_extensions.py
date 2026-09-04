"""Exact continuation search after entry into an absorbing zero-flag region.

NO_EXTENSION concerns one supplied prefix, NEVER the entire instance.
Written proofs accompany this implementation; it is not Lean-verified.
"""
from collections import deque
from border_lab import witness,border_witness


def zero_region(I):
    columns={r for _,r in I.flags}
    return frozenset(I.final-columns)


def absorption_holds(I):
    zero=zero_region(I)
    return all(r<0 or r in zero for f in I.final for r in I.delta[f])


def safe_states(I):
    return frozenset(set(range(len(I.delta)))-I.bad-{q for q,r in I.flags if q==r})


def primitive(word):
    for d in range(1,len(word)+1):
        if len(word)%d==0 and word==word[:d]*(len(word)//d): return word[:d]
    raise AssertionError('nonempty period required')


def active_rays(I,prefix):
    """Return unique phase-normalized periodic predictions, or reject the prefix."""
    if not absorption_holds(I): raise ValueError('Absorption hypothesis is required')
    run=I.run(prefix); safe=safe_states(I)
    if run is None or any(q not in safe for q in run): raise ValueError('Prefix is not defined and safe')
    if run[-1] not in zero_region(I): raise ValueError('Prefix must end in a zero-column final')
    n=len(prefix); rays=set()
    for j in range(1,n):
        for i in range(j):
            if (run[i],run[j]) in I.flags and prefix[i:].startswith(prefix[j:]):
                block=prefix[i:j]; phase=(n-i)%len(block)
                rays.add(primitive(block[phase:]+block[:phase]))
    return tuple(sorted(rays))


def advance(rays,letter):
    return tuple(sorted({p[1:]+p[0] for p in rays if p[0]==letter}))


def extension_decision(I,prefix,max_states=200000):
    """Exact all-length extension test; a resource cap yields UNKNOWN."""
    rays=active_rays(I,prefix)
    initial=(I.run(prefix)[-1],rays)
    parent={initial:None}; queue=deque([initial]); safe=safe_states(I)
    while queue:
        node=queue.popleft(); q,predictions=node
        if not predictions:
            letters=[]; x=node
            while parent[x] is not None:
                x,a=parent[x]; letters.append(a)
            suffix=''.join(reversed(letters)); word=prefix+suffix
            assert witness(I,word) and border_witness(I,word)
            return dict(status='YES',word=word,suffix=suffix,states=len(parent),initial_rays=list(rays))
        for a,r in zip(I.alphabet,I.delta[q]):
            if r not in safe: continue
            nxt=(r,advance(predictions,a))
            if nxt not in parent:
                if len(parent)>=max_states:
                    return dict(status='UNKNOWN',reason='extension graph state cap',states=len(parent))
                parent[nxt]=(node,a); queue.append(nxt)
    return dict(status='NO_EXTENSION',states=len(parent),initial_rays=list(rays))


def shortest_paths(I,start,allowed):
    if start not in allowed: return {}
    paths={start:''}; todo=deque([start])
    while todo:
        q=todo.popleft()
        for a,r in zip(I.alphabet,I.delta[q]):
            if r in allowed and r not in paths:
                paths[r]=paths[q]+a; todo.append(r)
    return paths


def components(I,allowed):
    """Kosaraju decomposition, without recursion depth assumptions."""
    seen=set(); finish=[]
    for root in sorted(allowed):
        if root in seen: continue
        seen.add(root); stack=[(root,iter(r for r in I.delta[root] if r in allowed))]
        while stack:
            q,it=stack[-1]
            r=next(it,None)
            if r is None: finish.append(q); stack.pop()
            elif r not in seen:
                seen.add(r); stack.append((r,iter(t for t in I.delta[r] if t in allowed)))
    rev={q:set() for q in allowed}
    for q in allowed:
        for r in I.delta[q]:
            if r in allowed: rev[r].add(q)
    done=set(); groups=[]
    for root in reversed(finish):
        if root in done: continue
        group={root}; done.add(root); todo=[root]
        for q in todo:
            for r in rev[q]:
                if r not in done: done.add(r); group.add(r); todo.append(r)
        groups.append(frozenset(group))
    return groups


def branching_certificate(I):
    """Cubic-length YES certificate from a safe cyclic branching vertex.

    The second edge may leave the cycle, including into a terminal region.
    Absence of this certificate is UNKNOWN, not a nonexistence result.
    """
    if not absorption_holds(I): return dict(status='UNKNOWN',reason='absorption hypothesis fails')
    safe=safe_states(I); paths=shortest_paths(I,I.start,safe)
    for group in components(I,safe&zero_region(I)):
        for q in sorted(group):
            internal=[(a,r) for a,r in zip(I.alphabet,I.delta[q]) if r in group]
            outgoing=[(a,r) for a,r in zip(I.alphabet,I.delta[q]) if r in safe]
            if q not in paths or not internal or len(outgoing)<2: continue
            a,r=internal[0]
            back=shortest_paths(I,r,group).get(q)
            if back is None: continue
            loop=a+back
            exit_letter=next(b for b,_ in outgoing if b!=a)
            prefix=paths[q]; rays=active_rays(I,prefix); count=len(rays)
            if not rays:
                return dict(status='YES',word=prefix,prefix=prefix,component=sorted(group),
                            initial_rays=0,proved_length_bound=len(prefix))
            for j in range(count+1):
                word=prefix+loop*j+exit_letter
                if witness(I,word):
                    assert border_witness(I,word)
                    bound=len(prefix)+count*len(loop)+1
                    assert len(word)<=bound
                    return dict(status='YES',word=word,prefix=prefix,loop=loop,
                                exit_letter=exit_letter,component=sorted(group),
                                initial_rays=count,proved_length_bound=bound)
            raise AssertionError('More incomparable tails than active periodic rays')
    return dict(status='UNKNOWN',reason='no reachable cyclic branching zero-region vertex')


def finite_frontier_decision(I,max_prefixes=10000,max_extension_states=200000):
    """Complete when the safe pre-zero frontier is acyclic, otherwise guarded.

    Cycles or resource limits leave UNKNOWN unless an independently checked
    witness is found. Complete exploration without either certifies NO.
    """
    if not absorption_holds(I): return dict(status='UNKNOWN',reason='absorption hypothesis fails')
    safe=safe_states(I); zero=zero_region(I)
    if I.start not in safe: return dict(status='NO',reason='unsafe initial state')
    rev={q:set() for q in safe}
    for q in safe:
        for r in I.delta[q]:
            if r in safe: rev[r].add(q)
    live=set(I.final&safe); todo=list(live)
    for q in todo:
        for r in rev[q]:
            if r not in live: live.add(r); todo.append(r)
    if I.start not in live: return dict(status='NO',reason='no safe accepting path')
    queue=deque([(I.start,'',frozenset({I.start}))]); count=0; blocked=False; entries=[]
    while queue:
        q,word,visited=queue.popleft(); count+=1
        if count>max_prefixes: return dict(status='UNKNOWN',reason='frontier prefix cap',prefixes=count)
        if q in I.final and witness(I,word):
            assert border_witness(I,word)
            return dict(status='YES',word=word,prefixes=count,entries=entries)
        if q in zero:
            r=extension_decision(I,word,max_extension_states)
            entries.append(dict(prefix=word,**r))
            if r['status']=='YES': return dict(status='YES',word=r['word'],prefixes=count,entries=entries)
            if r['status']=='UNKNOWN': blocked=True
            continue
        for a,r in zip(I.alphabet,I.delta[q]):
            if r not in live: continue
            if r in visited: blocked=True; continue
            queue.append((r,word+a,visited|{r}))
    return dict(status='UNKNOWN' if blocked else 'NO',prefixes=count,entries=entries,
                reason='pre-zero cycle or capped extension remains' if blocked else 'finite frontier and every extension exhausted')

"""Exact fixed-reference layers; UNPROVED representative-selection heuristic.

This is not an unrestricted decider. EXHAUSTED_HEURISTIC never means NO.
The fixed-reference graph and border decomposition have independent checkers.
"""
from collections import deque
from dataclasses import dataclass
from typing import Tuple
from border_lab import Instance, witness, border_witness


def prefix_function(word):
    pi = [0] * (len(word) + 1)
    for i in range(2, len(word) + 1):
        j = pi[i-1]
        while j and word[j] != word[i-1]:
            j = pi[j]
        if word[j] == word[i-1]:
            j += 1
        pi[i] = j
    return tuple(pi)


def border_chain(pi, length):
    out = []
    while length:
        out.append(length)
        length = pi[length]
    out.append(0)
    return tuple(out)


def ranks_and_milestones(word):
    pi = prefix_function(word)
    depths = [0]
    milestones = []
    for i in range(1, len(word)+1):
        depths.append(1 + depths[pi[i]])
        if depths[-1] > len(milestones):
            assert depths[-1] == len(milestones)+1
            milestones.append(i)
    return tuple(depths), tuple(milestones)


def valid_reverse_prefix(I, rho, labels):
    if len(labels) != len(rho)+1 or labels[0] not in I.final:
        return False
    if I.bad.intersection(labels):
        return False
    if any(I.delta[labels[i+1]][int(a)] != labels[i]
           for i,a in enumerate(rho)):
        return False
    pi = prefix_function(rho)
    return all((labels[i], labels[t]) not in I.flags
               for i in range(len(labels)) for t in border_chain(pi, i))


@dataclass(frozen=True)
class Reference:
    word: str
    labels: Tuple[int, ...]


def layer_graph(I, B, max_states=None, allow_return_completion=True):
    """Finish exactly, and collect shortest first-return representatives.

    The latter are ONE reference per endpoint state, not a complete family.
    No transition follows a completed second occurrence of the fixed B.
    """
    if not B.word or not valid_reverse_prefix(I, B.word, B.labels):
        raise ValueError('Reference must be a nonempty locally safe reverse path')
    k = len(I.delta)
    m = len(B.word)
    pi = prefix_function(B.word)
    incoming = [[[] for _ in range(2)] for _ in range(k)]
    for p,row in enumerate(I.delta):
        if p in I.bad:
            continue
        for a,q in enumerate(row):
            if q >= 0:
                incoming[q][a].append(p)
    # Per KMP state and new bit, the possible border lengths are fixed.
    advance = {}
    for j in range(m):
        for a in '01':
            t = j
            while t and B.word[t] != a:
                t = pi[t]
            if B.word[t] == a:
                t += 1
            advance[j,a] = (t, border_chain(pi,t))
    start = B.labels[-1], pi[m]
    parent = {start: None}
    todo = deque([start])
    growth = {}

    def reconstruct(state, final_step=None):
        tail = []
        while parent[state] is not None:
            old, a = parent[state]
            tail.append((a,state[0]))
            state = old
        tail.reverse()
        if final_step is not None:
            tail.append(final_step)
        word = B.word + ''.join(a for a,q in tail)
        labels = B.labels + tuple(q for a,q in tail)
        assert valid_reverse_prefix(I, word, labels)
        return Reference(word,labels)

    while todo:
        q,j = state = todo.popleft()
        if q == I.start:
            R = reconstruct(state)
            w = R.word[::-1]
            assert witness(I,w) and border_witness(I,w)
            return dict(status='FOUND_WITNESS',word=w,reference=R,
                        graph_states=len(parent),growth=growth)
        for a in '01':
            t,chain = advance[j,a]
            for p in incoming[q][int(a)]:
                if (p,p) in I.flags or any((p,B.labels[b]) in I.flags for b in chain):
                    continue
                if t == m:
                    if p not in growth:
                        R = reconstruct(state,(a,p))
                        if p == I.start and allow_return_completion:
                            w = R.word[::-1]
                            assert witness(I,w) and border_witness(I,w)
                            return dict(status='FOUND_WITNESS',word=w,reference=R,
                                        graph_states=len(parent),growth=growth)
                        growth[p] = R
                else:
                    nxt = p,t
                    if nxt not in parent:
                        if max_states is not None and len(parent) >= max_states:
                            return dict(status='UNKNOWN',reason='Layer state cap')
                        parent[nxt] = (state,a)
                        todo.append(nxt)
    return dict(status='LAYER_EXHAUSTED',graph_states=len(parent),growth=growth)


def shortest_endpoint_heuristic(I,max_calls=100000,max_states=100000):
    """Try an explicit global proof candidate, without mislabeling its gap."""
    k = len(I.delta)
    if any(any(t >= 0 for t in I.delta[f]) for f in I.final):
        raise ValueError('Terminal accepting states required')
    if witness(I,''):
        return dict(status='FOUND_WITNESS',word='',calls=0,trace=[])
    pending = []
    for f in sorted(I.final-I.bad):
        if (f,f) in I.flags:
            continue
        for p,row in enumerate(I.delta):
            for a,t in enumerate(row):
                if t == f:
                    R=Reference(str(a),(f,p))
                    if valid_reverse_prefix(I,R.word,R.labels):
                        pending.append((R,1,()))
    trace=[]
    calls=0
    while pending:
        B,depth,path=pending.pop(0)
        calls += 1
        if max_calls is not None and calls > max_calls:
            return dict(status='UNKNOWN',reason='Reference count cap',calls=calls)
        out=layer_graph(I,B,max_states)
        trace.append(dict(reference=B.word,labels=B.labels,depth=depth,
                          status=out['status'],endpoints=list(out.get('growth',{}))))
        if out['status']=='FOUND_WITNESS':
            return dict(status=out['status'],word=out['word'],calls=calls,trace=trace)
        if out['status']=='UNKNOWN':
            return dict(status='UNKNOWN',calls=calls,trace=trace)
        assert depth < k or not out['growth']
        if depth < k-1:
            for R in out['growth'].values():
                pending.append((R,depth+1,path+(B.word,)))
    return dict(status='EXHAUSTED_HEURISTIC',calls=calls,trace=trace,
                meaning='Only selected representatives exhausted; NOT a NO certificate')


def bounded_witness(I,length=16,node_cap=300000):
    todo=deque([('',I.start)])
    examined=0
    while todo:
        w,q=todo.popleft()
        examined+=1
        if examined>node_cap:
            return dict(status='UNKNOWN',reason='Node cap',examined=examined)
        if q in I.bad:
            continue
        if q in I.final and witness(I,w):
            return dict(status='FOUND_WITNESS',word=w,examined=examined)
        if len(w)<length:
            for a,p in enumerate(I.delta[q]):
                if p>=0:
                    todo.append((w+str(a),p))
    return dict(status='NO_WITHIN_LENGTH_BOUND',examined=examined)


def forward_action(I, rho):
    """Totalized action of reverse(rho), in the ORIGINAL forward automaton."""
    k=len(I.delta)
    out=[]
    for p in range(k+1):
        q=p
        for a in reversed(rho):
            q=I.delta[q][int(a)] if q<k else k
            if q<0:q=k
        out.append(q)
    return tuple(out)


def reverse_profile(rho,labels):
    pi=prefix_function(rho)
    return frozenset((labels[i],labels[t]) for i in range(len(labels))
                     for t in border_chain(pi,i))


def enriched_layer_graph(I,B,mode='action',max_states=20000):
    """Exact action/profile-refined layer search, heuristic output quotient.

    mode=action keeps endpoint and totalized forward action at promotion;
    mode=rich adds visited states and the whole internal agreement profile.
    Neither quotient is asserted to preserve future reference extensions.
    """
    if mode not in ('action','rich'):raise ValueError('Unknown signature')
    if not B.word or not valid_reverse_prefix(I,B.word,B.labels):
        raise ValueError('Invalid reference')
    k=len(I.delta);m=len(B.word);pi=prefix_function(B.word)
    incoming=[[[] for _ in range(2)] for _ in range(k)]
    letter_actions=[]
    for a in range(2):
        letter_actions.append(tuple((I.delta[p][a] if I.delta[p][a]>=0 else k)
                                    if p<k else k for p in range(k+1)))
    for p,row in enumerate(I.delta):
        if p in I.bad:continue
        for a,q in enumerate(row):
            if q>=0:incoming[q][a].append(p)
    advance={}
    for j in range(m):
        for a in '01':
            t=j
            while t and B.word[t]!=a:t=pi[t]
            if B.word[t]==a:t+=1
            advance[j,a]=t,border_chain(pi,t)
    action=forward_action(I,B.word)
    vis=sum(1<<q for q in set(B.labels)) if mode=='rich' else 0
    prof=sum(1<<(p*k+q) for p,q in reverse_profile(B.word,B.labels)) if mode=='rich' else 0
    start=(B.labels[-1],pi[m],action,vis,prof)
    todo=deque([start]);parent={start:None};growth={}
    def reconstruct(state,step=None):
        seq=[]
        while parent[state] is not None:
            old,a=parent[state];seq.append((a,state[0]));state=old
        seq.reverse()
        if step is not None:seq.append(step)
        R=Reference(B.word+''.join(a for a,p in seq),B.labels+tuple(p for a,p in seq))
        assert valid_reverse_prefix(I,R.word,R.labels)
        return R
    while todo:
        state=todo.popleft();q,j,A,V,P=state
        if q==I.start:
            R=reconstruct(state);w=R.word[::-1]
            assert witness(I,w) and border_witness(I,w)
            return dict(status='FOUND_WITNESS',word=w,reference=R,graph_states=len(parent),growth=growth)
        for a in '01':
            t,chain=advance[j,a]
            nextA=tuple(A[b] for b in letter_actions[int(a)])
            for p in incoming[q][int(a)]:
                if (p,p) in I.flags or any((p,B.labels[b]) in I.flags for b in chain):continue
                nextV=V|(1<<p) if mode=='rich' else 0
                nextP=P
                if mode=='rich':
                    nextP |= 1<<(p*k+p)
                    for b in chain:nextP |=1<<(p*k+B.labels[b])
                if t==m:
                    key=(p,nextA,nextV,nextP)
                    if key not in growth:
                        R=reconstruct(state,(a,p))
                        assert forward_action(I,R.word)==nextA
                        if p==I.start:
                            w=R.word[::-1]
                            assert witness(I,w) and border_witness(I,w)
                            return dict(status='FOUND_WITNESS',word=w,reference=R,graph_states=len(parent),growth=growth)
                        growth[key]=R
                else:
                    nxt=p,t,nextA,nextV,nextP
                    if nxt not in parent:
                        if max_states is not None and len(parent)>=max_states:
                            return dict(status='UNKNOWN',reason='Enriched layer state cap')
                        parent[nxt]=(state,a);todo.append(nxt)
    return dict(status='LAYER_EXHAUSTED',graph_states=len(parent),growth=growth)


def enriched_heuristic(I,mode='action',max_calls=10000,max_states=20000):
    k=len(I.delta)
    if any(any(t>=0 for t in I.delta[f]) for f in I.final):
        raise ValueError('Terminal finals required')
    if witness(I,''):return dict(status='FOUND_WITNESS',word='',calls=0,trace=[])
    pending=deque()
    for f in sorted(I.final-I.bad):
        if (f,f) in I.flags:continue
        for p,row in enumerate(I.delta):
            for a,t in enumerate(row):
                if t==f:
                    R=Reference(str(a),(f,p))
                    if valid_reverse_prefix(I,R.word,R.labels):pending.append((R,1))
    trace=[];calls=0
    while pending:
        B,h=pending.popleft();calls+=1
        if max_calls is not None and calls>max_calls:
            return dict(status='UNKNOWN',reason='Reference call cap',calls=calls)
        out=enriched_layer_graph(I,B,mode,max_states)
        trace.append(dict(reference=B.word,labels=B.labels,depth=h,status=out['status'],
                          growth_count=len(out.get('growth',{})),graph_states=out.get('graph_states')))
        if out['status']=='FOUND_WITNESS':return dict(status=out['status'],word=out['word'],calls=calls,trace=trace)
        if out['status']=='UNKNOWN':return dict(status='UNKNOWN',calls=calls,trace=trace)
        if h<k-1:
            pending.extend((R,h+1) for R in out['growth'].values())
        else:assert not out['growth']
    return dict(status='EXHAUSTED_HEURISTIC',calls=calls,trace=trace,
                meaning='Selected signatures exhausted; NOT a NO certificate')

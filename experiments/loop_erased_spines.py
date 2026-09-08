"""Exact finite simple-spine / regular-return decomposition of DFA paths.

For a run, repeatedly jump from the current occurrence of q to the LAST later
occurrence of q, recording the intervening closed walk as one return word, then
take the next single edge.  The resulting spine has no repeated state.

Thus every accepted word factors as

    M0 a0 M1 a1 ... Mr

where q0 -a0-> q1 -...-> qr is a simple accepting state path and each Mh is a
word taking qh back to qh.  Conversely every such factorization is accepted.
This is a language decomposition only; it does not by itself preserve or decide
BorderAvoid comparisons.
"""


def run(delta,start,word,alphabet='01'):
    index={ch:i for i,ch in enumerate(alphabet)}
    q=start; states=[q]
    for ch in word:
        if ch not in index: return None
        q=delta[q][index[ch]]
        if q < 0: return None
        states.append(q)
    return tuple(states)


def last_occurrence_decomposition(delta,start,word,final=None,alphabet='01'):
    """Canonical factorization of one defined run.

    Returns dict with distinct spine states, edge letters, and return words.
    If final is supplied, the word must end in final.
    """
    states=run(delta,start,word,alphabet)
    if states is None: raise ValueError('undefined word')
    if final is not None and states[-1] not in frozenset(final):
        raise ValueError('word is not accepted')
    pos=0; spine=[]; returns=[]; edges=[]
    while True:
        q=states[pos]
        last=max(i for i in range(pos,len(states)) if states[i]==q)
        spine.append(q)
        returns.append(word[pos:last])
        if last==len(word): break
        edges.append(word[last])
        pos=last+1
    if len(set(spine)) != len(spine):
        raise AssertionError('last-occurrence spine repeated a state')
    return {
        'states':tuple(spine),
        'edges':tuple(edges),
        'returns':tuple(returns),
    }


def reconstruct(parts):
    out=[]
    for i,M in enumerate(parts['returns']):
        out.append(M)
        if i < len(parts['edges']): out.append(parts['edges'][i])
    return ''.join(out)


def verify_decomposition(delta,start,word,final=None,alphabet='01'):
    parts=last_occurrence_decomposition(delta,start,word,final,alphabet)
    assert reconstruct(parts)==word
    index={ch:i for i,ch in enumerate(alphabet)}
    for h,q in enumerate(parts['states']):
        st=run(delta,q,parts['returns'][h],alphabet)
        assert st is not None and st[-1]==q
        if h < len(parts['edges']):
            assert delta[q][index[parts['edges'][h]]] == parts['states'][h+1]
    return parts


def simple_accepting_spines(delta,start,final,alphabet='01'):
    """Enumerate all labelled simple accepting state paths."""
    final=frozenset(final); out=[]
    stack=[(start,(start,),())]
    while stack:
        q,states,edges=stack.pop()
        if q in final:
            out.append({'states':states,'edges':edges})
            # Terminal-final slices have no useful continuation.  For a generic
            # DFA we still stop here because this cover is for paths ending at
            # their chosen accepting cut.
            continue
        for a in reversed(range(len(alphabet))):
            r=delta[q][a]
            if r < 0 or r in states: continue
            stack.append((r,states+(r,),edges+(alphabet[a],)))
    return tuple(sorted(out,key=lambda x:(x['states'],x['edges'])))


def spine_key(parts):
    return parts['states'],parts['edges']

"""Exact constant-from-end NO selector synthesis for terminal candidate languages.

Given a deterministic partial DFA and ordered forbidden state pairs, this module
computes the maximal common suffix shared by every accepted word and the state
sequences with which that suffix can occur.  If every possible suffix-entry
state yields a flagged suffix-prefix agreement entirely inside the forced tail,
we obtain an all-word NO certificate.

This is a finite regular-language rule.  It is not a complete BorderAvoid
solver and does not assume a candidate-length cutoff.
"""
from collections import deque


def _check(delta, start, final, alphabet):
    k=len(delta)
    if not (0 <= start < k): raise ValueError('bad start')
    final=frozenset(final)
    if not final.issubset(range(k)): raise ValueError('bad final')
    if any(len(row)!=len(alphabet) for row in delta): raise ValueError('width')
    for row in delta:
        for q in row:
            if q < -1 or q >= k: raise ValueError('target')
    return final


def shortest_word(delta,start,final,alphabet='01'):
    final=_check(delta,start,final,alphabet)
    if start in final: return ''
    parent={start:None}; todo=deque([start])
    while todo:
        p=todo.popleft()
        for a,ch in enumerate(alphabet):
            q=delta[p][a]
            if q < 0 or q in parent: continue
            parent[q]=(p,ch)
            if q in final:
                out=[]; cur=q
                while parent[cur] is not None:
                    cur,ch0=parent[cur]; out.append(ch0)
                return ''.join(reversed(out))
            todo.append(q)
    return None


def _suffix_dfa_step(pattern, matched, ch):
    """KMP-style state: longest prefix of pattern suffixing text read so far."""
    s=pattern[:matched] + ch
    best=0
    for r in range(min(len(pattern),len(s))+1):
        if s.endswith(pattern[:r]): best=r
    return best


def suffix_counterexample(delta,start,final,pattern,alphabet='01'):
    """Accepted word not ending in pattern, or None iff all accepted words do."""
    final=_check(delta,start,final,alphabet)
    first=(start,0); parent={first:None}; todo=deque([first])
    while todo:
        p,m=state=todo.popleft()
        if p in final and m != len(pattern):
            out=[]
            while parent[state] is not None:
                state,ch=parent[state]; out.append(ch)
            return ''.join(reversed(out))
        for a,ch in enumerate(alphabet):
            q=delta[p][a]
            if q < 0: continue
            nm=_suffix_dfa_step(pattern,m,ch)
            nxt=(q,nm)
            if nxt not in parent:
                parent[nxt]=(state,ch); todo.append(nxt)
    return None


def maximal_common_suffix(delta,start,final,alphabet='01'):
    """Return maximal literal suffix common to every accepted word.

    None means the language is empty.  The empty string is returned when epsilon
    is accepted or when no nonempty suffix is universal.
    """
    w=shortest_word(delta,start,final,alphabet)
    if w is None: return None
    if w == '': return ''
    best=''
    for length in range(1,len(w)+1):
        z=w[-length:]
        if suffix_counterexample(delta,start,final,z,alphabet) is None:
            best=z
        else:
            break
    return best


def reachable_states(delta,start):
    seen={start}; todo=[start]
    for p in todo:
        for q in delta[p]:
            if q >= 0 and q not in seen:
                seen.add(q); todo.append(q)
    return frozenset(seen)


def suffix_entry_sequences(delta,start,final,suffix,alphabet='01'):
    """All state sequences q0..q_|suffix| of accepted words x suffix."""
    final=_check(delta,start,final,alphabet)
    index={ch:i for i,ch in enumerate(alphabet)}
    out=[]
    for q0 in sorted(reachable_states(delta,start)):
        seq=[q0]; q=q0
        ok=True
        for ch in suffix:
            q=delta[q][index[ch]]
            if q < 0:
                ok=False; break
            seq.append(q)
        if ok and q in final:
            out.append(tuple(seq))
    return tuple(out)


def forced_tail_violation(delta,start,final,flags,alphabet='01'):
    """Find a comparison entirely inside the maximal forced suffix.

    Returns a certificate only if the SAME relative cuts (i,j) are forbidden
    for every possible entry-state sequence of that forced suffix.
    """
    suffix=maximal_common_suffix(delta,start,final,alphabet)
    if suffix is None:
        return {'status':'EMPTY_LANGUAGE'}
    seqs=suffix_entry_sequences(delta,start,final,suffix,alphabet)
    flags=frozenset(flags)
    L=len(suffix)
    for i in range(L+1):
        for j in range(i+1,L):
            target=suffix[j:]
            if not suffix[i:].startswith(target):
                continue
            pairs=tuple((seq[i],seq[j]) for seq in seqs)
            if seqs and all(pair in flags for pair in pairs):
                return {
                    'status':'NO_CERTIFICATE',
                    'common_suffix':suffix,
                    'relative_cuts':(i,j),
                    'target_length':L-j,
                    'state_pairs':pairs,
                    'entry_sequences':seqs,
                }
    return {
        'status':'NO_CERTIFICATE_NOT_FOUND',
        'common_suffix':suffix,
        'entry_sequences':seqs,
    }

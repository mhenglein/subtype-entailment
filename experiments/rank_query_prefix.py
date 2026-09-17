"""Prefix identities and the previous exact fixed-reference finite layer.

Copied with attribution from the previous uncommitted rank checkpoint.
No reference-selection heuristic or unrestricted decider is included here.
This module is an independent finite-layer oracle for the new graph tests.
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

"""Exact witness decision for <=3 states; proof in notes/2026-09-04-three-state.md.

The bound is six letters, not a truncation of the general problem. Arbitrary
larger instances are rejected. The proof also applies to any finite alphabet.
"""
from collections import deque
from itertools import product
from pathlib import Path
import json
from border_lab import Instance, Sandwich, witness, border_witness, sufficient, lrs, words

ROOT=Path(__file__).resolve().parents[1]


def three_state_decision(instance):
    """Return an exact answer for a well-formed automaton with <=3 states."""
    k=len(instance.delta)
    if not 1 <= k <= 3:
        raise ValueError('This exact decision procedure requires 1 to 3 states.')
    if not instance.alphabet or len(set(instance.alphabet)) != len(instance.alphabet):
        raise ValueError('The alphabet must contain distinct letters.')
    if not 0 <= instance.start < k or any(len(row)!=len(instance.alphabet) for row in instance.delta):
        raise ValueError('Malformed start state or transition row.')
    if any(q < -1 or q >= k for row in instance.delta for q in row):
        raise ValueError('Malformed transition target.')
    if any(q < 0 or q >= k for q in instance.final | instance.bad):
        raise ValueError('Malformed final or bad state.')
    if any(not (0 <= q < k and 0 <= r < k) for q,r in instance.flags):
        raise ValueError('Malformed flag relation.')
    for word in words(instance.alphabet,6):
        if witness(instance,word):
            assert border_witness(instance,word)
            return {'status':'YES','word':word,'length':len(word)}
    return {'status':'NO','reason':'proved six-letter bound for at most three states'}


def boundary_reachable(instance):
    seen={0}; todo=[0]
    for q in todo:
        for r in instance.delta[q]:
            if r>=0 and r not in seen:
                seen.add(r); todo.append(r)
    return 2 in seen


def normalized_classification(instance):
    """Structural classification for three safe states, start 0, final 2.

    Diagonal flags and all flags into state 2 have already been removed by
    the exact final-state boundary slice. This function is independent of
    the bounded enumeration used by three_state_decision.
    """
    for word in words(instance.alphabet,2):
        if witness(instance,word):
            return word,'short-boundary-witness'
    if not boundary_reachable(instance):
        return None,'boundary-empty'
    letters=range(len(instance.alphabet))
    possible=[a for a in letters if instance.delta[0][a]==1 and instance.delta[1][a]==2]
    assert len(possible)==1 and (0,1) in instance.flags
    a=possible[0]; A=instance.alphabet[a]
    others=[b for b in letters if b!=a]
    assert all(instance.delta[0][b] in {-1,0} and instance.delta[1][b] in {-1,0,1} for b in others)
    for b in others:
        if instance.delta[2][b]==2:
            return A+A+instance.alphabet[b],'final-other-letter-loop'
    if instance.delta[2][a]==2:
        for b in others:
            if instance.delta[1][b]==1:
                return A+instance.alphabet[b]+A+A,'middle-other-letter-loop'
        for b in others:
            if instance.delta[2][b]==1:
                return A+A+instance.alphabet[b]+A+A+A,'final-to-middle-return'
    return None,'unary-final-excursion-obstruction'


def exhaustive_check():
    flag_options=((0,1),(1,0),(2,0),(2,1))
    counts={}; total=0; largest=0; max_no_states=0
    for entries in product(range(-1,3),repeat=6):
        delta=tuple(tuple(entries[2*q:2*q+2]) for q in range(3))
        for bits in product((False,True),repeat=4):
            flags=frozenset(p for p,yes in zip(flag_options,bits) if yes)
            I=Instance(delta,frozenset({2}),flags)
            candidate,reason=normalized_classification(I)
            counts[reason]=counts.get(reason,0)+1
            total+=1
            if candidate is not None:
                assert witness(I,candidate) and border_witness(I,candidate)
                assert len(candidate)<=6 and lrs(candidate)<=2
                assert sufficient(I,candidate,2,0)
                largest=max(largest,len(candidate))
            else:
                r=Sandwich(I,1,1,False).search(10000)
                assert r['status']=='NO',(I,r,reason)
                max_no_states=max(max_no_states,r['states'])
    out=dict(status='PASS',normalized_instances=total,classes=counts,
             largest_constructed_witness_length=largest,
             positive_checks='forward, reversed, Sufficient(2,0)',
             negative_checks='complete Necessary(1,1) graph exhaustion',
             maximum_negative_graph_states=max_no_states,
             normalization='single final 2, start 0, no bad/diagonal/incoming-final flags; all 4^6 partial transitions and 2^4 remaining flag relations',
             scope='exhaustive finite verification plus separate written general proof; not Lean-checked')
    (ROOT/'results/three-state-exhaustive.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


def decide_small_slices(instance):
    """Sound YES/NO/UNKNOWN front-end for arbitrary finite instances.

    Complete when every nonempty final-state boundary slice has at most
    three live states. Larger unresolved slices produce UNKNOWN.
    Inputs must satisfy the repository's well-formed Instance convention.
    """
    k=len(instance.delta)
    slices=[]
    for final in sorted(instance.final):
        banned=set(instance.bad)
        banned.update(q for q in range(k) if (q,q) in instance.flags or (q,final) in instance.flags)
        if instance.start in banned or final in banned:
            slices.append({'final':final,'status':'NO','reason':'forbidden boundary endpoint'})
            continue
        allowed=set(range(k))-banned
        forward={instance.start}; todo=[instance.start]
        for q in todo:
            for r in instance.delta[q]:
                if r in allowed and r not in forward:
                    forward.add(r); todo.append(r)
        reverse={q:set() for q in allowed}
        for q in allowed:
            for r in instance.delta[q]:
                if r in allowed: reverse[r].add(q)
        backward={final}; todo=[final]
        for q in todo:
            for r in reverse[q]:
                if r not in backward:
                    backward.add(r); todo.append(r)
        live=forward & backward
        if instance.start not in live:
            slices.append({'final':final,'status':'NO','reason':'boundary graph empty'})
            continue
        if len(live)>3:
            slices.append({'final':final,'status':'UNKNOWN','live_states':len(live)})
            continue
        retained=sorted(live); index={q:i for i,q in enumerate(retained)}
        compact=Instance(tuple(tuple(index.get(r,-1) for r in instance.delta[q]) for q in retained),
                         frozenset({index[final]}),
                         frozenset((index[q],index[r]) for q,r in instance.flags if q in live and r in live),
                         frozenset(),index[instance.start],instance.alphabet)
        answer=three_state_decision(compact)
        row=dict(final=final,live_states=len(live),**answer)
        slices.append(row)
        if answer['status']=='YES':
            assert witness(instance,answer['word']) and border_witness(instance,answer['word'])
            return {'status':'YES','word':answer['word'],'slices':slices}
    status='UNKNOWN' if any(row['status']=='UNKNOWN' for row in slices) else 'NO'
    return {'status':status,'slices':slices}


if __name__=='__main__':
    exhaustive_check()

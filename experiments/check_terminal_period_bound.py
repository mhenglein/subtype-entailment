"""Check the terminal bounded-exponent lemma for flagged suffix agreements.

Written proof is in notes/2026-09-05-terminal-period-bound.md. This script is
finite evidence only. Standard library only.
"""
import json, random
from pathlib import Path

from border_lab import Instance, words

ROOT = Path(__file__).resolve().parents[1]


def agreements(I, w):
    c = I.run(w)
    n = len(w)
    out = []
    for i in range(n):
        for j in range(i + 1, n + 1):
            if (c[i], c[j]) not in I.flags:
                continue
            target = w[j:]
            if w[i:i+len(target)] == target:
                out.append((i, j))
    return out


def check_agreement(I, w, i, j):
    c = I.run(w)
    n = len(w); k = len(I.delta); d = j-i; N = n-i
    assert all(w[x] == w[x+d] for x in range(i, n-d))
    starts = list(range(i, n+1, d))
    for a in range(len(starts)-1):
        p, q = starts[a], starts[a+1]
        assert w[q:] == w[p:p+n-q]
        assert c[p] != c[q]
    assert len({c[x] for x in starts}) == len(starts)
    assert len(starts) <= k
    assert N // d <= k-1
    t, rlen = divmod(N, d)
    y = w[i:j]
    r = y[:rlen]
    assert w[i:] == y*t + r
    assert t <= k-1
    return dict(i=i,j=j,gap=d,source_length=N,full_period_copies=t,remainder=rlen)


def terminal(I):
    return all(all(q < 0 for q in I.delta[f]) for f in I.final)


def accepted(I, w):
    c = I.run(w)
    return c is not None and c[-1] in I.final and all(q not in I.bad for q in c)


def main():
    rng = random.Random(2026090541)
    checked_words=0; checked_agreements=0; max_t=0; examples=[]
    for case in range(2000):
        k=rng.randrange(2,8)
        final=rng.randrange(k)
        delta=[]
        for q in range(k):
            if q==final:
                delta.append((-1,-1)); continue
            delta.append(tuple(-1 if rng.random()<.16 else rng.randrange(k) for _ in range(2)))
        flags=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.12)
        bad=frozenset(q for q in range(k) if q != final and rng.random()<.05)
        I=Instance(tuple(delta),frozenset({final}),flags,bad)
        assert terminal(I)
        for w in words('01',9):
            if not accepted(I,w): continue
            checked_words += 1
            for i,j in agreements(I,w):
                row=check_agreement(I,w,i,j)
                checked_agreements += 1
                max_t=max(max_t,row['full_period_copies'])
                if len(examples)<12 and row['full_period_copies']>=max(2,k-2):
                    examples.append(dict(k=k,word=w,states=I.run(w),pair=[i,j],**row))
    sharp=[]
    for k in range(2,9):
        delta=tuple([(q+1,-1) for q in range(k-1)]+[(-1,-1)])
        I=Instance(delta,frozenset({k-1}),frozenset({(0,1)}))
        w='0'*(k-1)
        row=check_agreement(I,w,0,1)
        assert row['full_period_copies']==k-1
        sharp.append(dict(k=k,word=w,t=k-1))
    out=dict(status='PASS',seed=2026090541,random_instances=2000,
             accepted_words=checked_words,flagged_agreements=checked_agreements,
             maximum_full_period_copies=max_t,sharp_family=sharp,examples=examples,
             theorem='For terminal accepted w and flagged suffix agreement i<j, floor((|w|-i)/(j-i)) <= k-1.',
             proof_status='Written proof; finite checks are supporting evidence only.')
    (ROOT/'results/terminal-period-bound.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('status','accepted_words','flagged_agreements','maximum_full_period_copies')},indent=2))

if __name__=='__main__': main()

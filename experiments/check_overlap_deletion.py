"""Reproduce the overlapping-deletion counterexample and corrected masks."""
from itertools import product, combinations
from pathlib import Path
from random import Random
import json

from overlap_deletion import alignment_closure, certify, four_block_instance, intervals, survivor
from border_lab import words

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026090901


def compatible(mask, agreements):
    return all(((a+t in mask) == (b+t in mask))
               for a, b, r in agreements for t in range(r))


def graph_closure(n, agreements, seeds):
    graph = [set() for _ in range(n)]
    for a, b, r in agreements:
        for t in range(r):
            graph[a+t].add(b+t)
            graph[b+t].add(a+t)
    reached = set(seeds)
    queue = list(seeds)
    for p in queue:
        for q in graph[p]:
            if q not in reached:
                reached.add(q)
                queue.append(q)
    return frozenset(reached)


def check():
    counts = dict(family_counterexamples=0, large_shift_family_cases=0,
                  large_shift_window_pairs=0, repaired_family_certificates=0,
                  exhaustive_mask_minima=0, binary_survivor_checks=0,
                  multiple_alignment_cases=0, guards=0)
    I = four_block_instance()
    examples = []
    for m in range(3, 81):
        p = m+1
        word = ('0'*m+'1')*4
        agreement = (0, p, 3*p)
        old = I.run(word)
        seed = {p+1, 2*p+1}
        cuts = intervals(seed)
        assert I.admissible(word)
        assert word[:3*p] == word[p:4*p]
        assert all(old[a] == old[b] for a, b in cuts)
        assert all(0 < a < b < 3*p and p < a < b < 4*p for a, b in cuts)
        shortened = survivor(word, 0, len(word), seed)
        assert I.admissible(shortened)
        left = survivor(word, 0, 3*p, seed)
        right = survivor(word, p, 4*p, seed)
        assert len(left) == len(right) and left != right
        counts['family_counterexamples'] += 1
        counts['large_shift_family_cases'] += p > len(I.delta)**2
        repair = certify(I, word, [agreement], seed)
        assert repair['status'] == 'CERTIFIED'
        assert repair['deleted'] == [1, p+1, 2*p+1, 3*p+1]
        assert repair['word'] == ('0'*(m-1)+'1')*4
        counts['repaired_family_certificates'] += 1
        if m in (3, 80):
            examples.append(dict(m=m, states=len(I.delta), period=p,
                original_length=len(word), original_equalities=[agreement],
                invalid_paired_deletions=cuts, survivor_lengths=[len(left),len(right)],
                first_mismatch=next(i for i, (a,b) in enumerate(zip(left,right)) if a!=b),
                repaired_deletions=repair['intervals'], repaired_length=len(repair['word'])))
    # Every collision choice in the proposed n^2+1 interior window fails.
    m=80; p=m+1; word=('0'*m+'1')*4; old=I.run(word)
    for t, u in combinations(range(p+1, p+1+len(I.delta)**2+1), 2):
        seed=set(range(t,u)) | set(range(p+t,p+u))
        assert u-t < p and old[t]==old[u] and old[p+t]==old[p+u]
        assert survivor(word,0,3*p,seed) != survivor(word,p,4*p,seed)
        assert I.admissible(survivor(word,0,len(word),seed))
        counts['large_shift_window_pairs'] += 1
    # Exhaustively verify least-mask claims against all masks on short domains.
    for n in range(1, 7):
        for a in range(n):
            for b in range(a+1, n):
                for r in range(1, n-b+1):
                    agreements=[(a,b,r)]
                    for seed in range(n):
                        minimal=set(range(n))
                        for bits in range(1<<n):
                            mask={q for q in range(n) if bits>>q&1}
                            if seed in mask and compatible(mask,agreements):
                                minimal &= mask
                        actual=alignment_closure(n,agreements,{seed})
                        assert actual==minimal==graph_closure(n,agreements,{seed})
                        counts['exhaustive_mask_minima'] += 1
                        for word in words('01',n):
                            if len(word)!=n or word[a:a+r]!=word[b:b+r]:
                                continue
                            assert survivor(word,a,a+r,actual)==survivor(word,b,b+r,actual)
                            counts['binary_survivor_checks'] += 1
    rng=Random(SEED)
    for _ in range(500):
        n=rng.randrange(2,31)
        word=''.join(rng.choice('01') for _ in range(n))
        agreements=[]
        for a in range(n):
            for b in range(a+1,n):
                for r in range(1,n-b+1):
                    if word[a:a+r]==word[b:b+r]:
                        agreements.append((a,b,r))
        rng.shuffle(agreements);agreements=agreements[:rng.randrange(1,5)]
        seed={rng.randrange(n),rng.randrange(n)}
        actual=alignment_closure(n,agreements,seed)
        assert actual==graph_closure(n,agreements,seed) and compatible(actual,agreements)
        for a,b,r in agreements:
            assert survivor(word,a,a+r,actual)==survivor(word,b,b+r,actual)
        counts['multiple_alignment_cases'] += 1
    w=('0001')*4
    assert certify(I,w,[(0,4,12)],{5,9},protected_letters={1})['status']=='NOT_CERTIFIED'
    counts['guards']+=1
    assert certify(I,w,[(0,4,12)],{7})['status']=='NOT_CERTIFIED'
    counts['guards']+=1
    assert certify(I,w,[(0,4,12)],set())['status']=='NOT_CERTIFIED'
    counts['guards']+=1
    for f in (lambda:alignment_closure(4,[(0,2,3)],{1}),
              lambda:alignment_closure(4,[(0,2,2)],{4}),
              lambda:certify(I,w,[(0,3,2)],{1})):
        try:f()
        except ValueError:counts['guards']+=1
        else:raise AssertionError('Malformed input accepted')
    result=dict(status='PASS',seed=SEED,counts=counts,examples=examples,
        proof_status='Written counterexample and corrected mask theorem; independent review pending; not Lean-checked',
        scope='Selected equality/acceptance preservation, not preservation of every witness obligation or an unrestricted bound')
    (ROOT/'results'/'overlap-deletion-audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    check()

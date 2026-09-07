"""Deterministic regression for the terminal bad-language decomposition.

The all-length theorem is in notes/2026-09-07-terminal-bad-language-decomposition.md.
This script supplies finite supporting evidence only. It constructs a fixed
corpus from a seeded pool, checks all binary words through length eight, and
verifies every proper violation against the non-overlap / bounded-overlap split.
Standard library only. No resource cap is interpreted as a theorem.
"""
import json
import random
from collections import defaultdict
from itertools import product
from pathlib import Path

from border_lab import Instance

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026090701
WORDS = tuple(''.join(x) for n in range(9) for x in product('01', repeat=n))

# Quotas fix a deterministic regression corpus after the seeded pool is built.
# Tuple = (admissible, bad, representative_nonoverlap, representative_overlap).
QUOTAS = {
 (1,0,0,0):299,(13,13,0,0):2,(33,33,0,0):2,(4,0,0,0):5,(4,4,3,0):1,
 (1,1,0,0):230,(2,2,0,0):82,(8,8,0,0):1,(20,20,0,0):7,(10,0,0,0):1,
 (7,0,0,0):2,(8,0,0,0):1,(15,0,0,0):1,(2,0,0,0):41,(12,0,0,0):1,
 (3,3,3,0):2,(4,4,2,0):1,(16,16,0,0):1,(6,6,0,0):5,(16,0,0,0):1,
 (4,4,1,1):1,(4,4,0,0):15,(13,0,0,0):1,(14,14,0,0):2,(2,1,0,0):10,
 (3,3,0,0):12,(21,20,0,0):1,(7,7,0,0):4,(23,23,0,0):1,(1,1,1,0):7,
 (14,0,0,0):1,(16,15,0,0):2,(4,3,0,0):4,(12,12,5,0):1,(9,9,0,0):1,
 (21,21,0,0):1,(8,8,4,0):1,(12,12,6,0):1,(30,0,0,0):6,(2,2,1,0):6,
 (11,0,0,0):1,(12,12,4,1):1,(12,12,0,0):1,(22,22,13,1):1,(11,11,0,0):2,
 (16,6,6,0):1,(9,8,8,0):1,(15,15,0,0):1,(3,2,0,0):5,(7,7,7,0):1,
 (5,4,0,0):2,(22,22,16,1):1,(2,2,2,0):2,(28,28,21,0):3,(6,6,0,5):1,
 (5,0,0,0):1,(3,3,1,0):3,(4,2,2,0):1,(33,33,29,1):1,(8,7,0,0):3,
 (21,21,5,1):1,(6,6,5,0):2,(52,0,0,0):1,(6,6,6,0):1,(7,6,6,0):1,
 (3,1,0,0):1,(3,0,0,0):11,(4,4,4,0):1,(7,7,0,1):1,(5,5,0,0):2,
 (33,33,17,0):1,(6,0,0,0):2,(21,20,17,0):2,(2,1,1,0):4,(10,10,0,0):1,
 (3,3,2,0):1,(3,2,2,0):1,(8,8,3,0):1,(12,12,4,0):1,(5,5,2,0):1,
 (7,7,3,0):1,(10,10,2,1):1,(17,17,0,0):1,(9,7,0,0):1,(21,21,5,3):1,
 (13,13,9,1):1,(28,28,3,1):1,(10,10,4,0):1,(9,0,0,0):1,(36,36,0,1):1,
 (3,1,1,0):1,(7,6,5,0):1,(32,32,32,0):1,(14,14,9,0):1,(36,36,29,1):1,
 (7,7,6,0):1,(7,7,2,1):1,(5,5,3,1):1,
}


def violations(I, word):
    c = I.run(word)
    if c is None or c[-1] not in I.final:
        return None, ()
    n = len(word)
    return c, tuple((i,j) for i in range(n+1) for j in range(i,n+1)
                    if (c[i],c[j]) in I.flags and word[i:].startswith(word[j:]))


def contribution(I):
    admissible = bad = non = overlap = 0
    for word in WORDS:
        c, vs = violations(I, word)
        if c is None:
            continue
        admissible += 1
        if vs:
            bad += 1
        proper = [(i,j) for i,j in vs if i < j < len(word)]
        if proper:
            i,j = proper[0]
            if j-i < len(word)-j:
                overlap += 1
            else:
                non += 1
    return admissible, bad, non, overlap


def random_instance(rng):
    k = rng.randint(2,6)
    p_undef = rng.choice((.1,.2,.3,.4))
    p_flag = rng.choice((.05,.1,.2,.3))
    delta = []
    for _ in range(k-1):
        delta.append(tuple(-1 if rng.random() < p_undef else rng.randrange(k)
                           for _ in range(2)))
    delta.append((-1,-1))
    flags = frozenset((p,q) for p in range(k) for q in range(k)
                      if rng.random() < p_flag)
    return Instance(tuple(delta), frozenset({k-1}), flags)


def build_corpus():
    rng = random.Random(SEED)
    pool = []
    seen = set()
    grouped = defaultdict(list)
    for _ in range(5000):
        I = random_instance(rng)
        key = (I.delta, I.final, I.flags)
        if key in seen:
            continue
        seen.add(key)
        m = contribution(I)
        if m[0] == 0:
            continue
        pool.append(I)
        grouped[m].append(I)
    corpus = []
    for m, needed in QUOTAS.items():
        assert len(grouped[m]) >= needed, (m, needed, len(grouped[m]))
        corpus.extend(grouped[m][:needed])
    assert len(corpus) == 852
    return corpus


def check():
    counts = dict(corpus_entries=0, words_checked=0, admissible_candidates=0,
                  bad_accepted_candidates=0, representative_nonoverlap=0,
                  representative_overlap=0, all_nonoverlap=0, all_overlap=0,
                  maximum_overlap_exponent=0, decomposition_mismatches=0)
    for I in build_corpus():
        counts['corpus_entries'] += 1
        k = len(I.delta)
        # Construction itself enforces terminality of the sole accepting state.
        assert all(q < 0 for f in I.final for q in I.delta[f])
        for word in WORDS:
            counts['words_checked'] += 1
            c, vs = violations(I, word)
            if c is None:
                continue
            counts['admissible_candidates'] += 1
            if vs:
                counts['bad_accepted_candidates'] += 1
            proper = [(i,j) for i,j in vs if i < j < len(word)]
            if proper:
                i,j = proper[0]
                if j-i < len(word)-j:
                    counts['representative_overlap'] += 1
                else:
                    counts['representative_nonoverlap'] += 1
            for i,j in proper:
                d = j-i
                zlen = len(word)-j
                if d >= zlen:
                    counts['all_nonoverlap'] += 1
                    x, z = word[:i], word[j:]
                    middle = word[i+zlen:j]
                    if word != x + z + middle + z:
                        counts['decomposition_mismatches'] += 1
                else:
                    counts['all_overlap'] += 1
                    source_len = len(word)-i
                    exponent, remainder = divmod(source_len, d)
                    gap = word[i:j]
                    if word[i:] != gap*exponent + gap[:remainder]:
                        counts['decomposition_mismatches'] += 1
                    aligned = [c[i+t*d] for t in range(exponent+1)]
                    if len(set(aligned)) != len(aligned) or exponent > k-1:
                        counts['decomposition_mismatches'] += 1
                    counts['maximum_overlap_exponent'] = max(
                        counts['maximum_overlap_exponent'], exponent)
    expected = {
        'corpus_entries': 852,
        'words_checked': 435372,
        'admissible_candidates': 2630,
        'bad_accepted_candidates': 1770,
        'representative_nonoverlap': 407,
        'representative_overlap': 22,
        'all_nonoverlap': 749,
        'all_overlap': 32,
        'maximum_overlap_exponent': 4,
        'decomposition_mismatches': 0,
    }
    assert counts == expected, (counts, expected)
    return {
        'status': 'PASS', 'date': '2026-09-07', 'seed': SEED,
        'counts': counts,
        'proof_status': 'Written all-length argument; finite regression is supporting evidence only; not Lean-checked or independently reviewed',
        'scope': 'Terminal binary BorderAvoid proper violations; no unrestricted containment/decision theorem'
    }


if __name__ == '__main__':
    out = check()
    path = ROOT/'results'/'terminal-bad-language-decomposition.json'
    path.write_text(json.dumps({
        'status': out['status'], 'date': out['date'], 'seed': out['seed'],
        'corpus_entries': out['counts']['corpus_entries'],
        'words_checked': out['counts']['words_checked'],
        'admissible_candidates': out['counts']['admissible_candidates'],
        'bad_accepted_candidates': out['counts']['bad_accepted_candidates'],
        'representative_proper_violations': {
            'non_overlap': out['counts']['representative_nonoverlap'],
            'overlap': out['counts']['representative_overlap']},
        'all_proper_violations': {
            'non_overlap': out['counts']['all_nonoverlap'],
            'overlap': out['counts']['all_overlap']},
        'maximum_observed_overlap_exponent': out['counts']['maximum_overlap_exponent'],
        'decomposition_mismatches': out['counts']['decomposition_mismatches'],
        'proof_status': out['proof_status'], 'scope': out['scope']
    }, indent=2)+'\n')
    print(json.dumps(out, indent=2))

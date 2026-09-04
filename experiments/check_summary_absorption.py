"""Check a joint F/transition/G invariant and a denial-free exact subclass.

The independent NFA code implements the reviewed normalized rules, not the
full bridge or denial saturation. All generated systems omit denials.
Written proofs establish the all-input results; tests are bounded evidence.
"""
from collections import deque
import json
import random
from typing import FrozenSet, Tuple
from border_lab import Instance, witness, border_witness, sufficient, Sandwich
from continue_research import ROOT, BASE, encode
from check_budget_growth_family import family

Rule = Tuple[int, int, str, int]


def pop_summary(k: int, rules: Tuple[Rule, ...]):
    eps = [{i} for i in range(k)]
    edges = [[set(), set()] for _ in range(k)]
    for p, q, op, a in rules:
        if op == 'eps': eps[p].add(q)
        if op == 'pop': edges[p][a].add(q)
    while True:
        old = tuple(frozenset(s) for s in eps)
        for p in range(k):
            for q in tuple(eps[p]): eps[p].update(eps[q])
        for p, q, op, a in rules:
            if op == 'push':
                for r in tuple(eps[q]):
                    for s in edges[r][a]: eps[p].update(eps[s])
        if tuple(frozenset(s) for s in eps) == old: break
    return tuple(frozenset(s) for s in eps), edges


def independent_bridge(k: int, constraints, alpha=0, beta=1):
    rules = []
    forced = set()
    for op, p, q, r in constraints:
        if op == 'lower':
            rules.extend(((p, r, 'push', 0), (q, r, 'push', 1)))
            forced.add(r)
        elif op == 'upper':
            rules.extend(((p, q, 'pop', 0), (p, r, 'pop', 1)))
        elif op == 'leq': rules.append((p, q, 'eps', -1))
        else: raise ValueError('This independent check omits denials.')
    reverse = tuple((q, p, {'push':'pop','pop':'push','eps':'eps'}[op], a)
                    for p, q, op, a in rules)
    be, bt = pop_summary(k, tuple(rules))
    ae, at = pop_summary(k, reverse)
    def step(subset, letter, eps, edges):
        result = set()
        for p in subset:
            for q in edges[p][letter]: result.update(eps[q])
        return frozenset(result)
    classes = [(be[alpha], ae[beta])]
    ids = {classes[0]: 0}
    delta = []
    index = 0
    while index < len(classes):
        b, a = classes[index]
        row = []
        for letter in (0, 1):
            c = (step(b, letter, be, bt), step(a, letter, ae, at))
            if c not in ids:
                ids[c] = len(classes)
                classes.append(c)
            row.append(ids[c])
        delta.append(tuple(row))
        index += 1
    finals = frozenset(i for i, (_, a) in enumerate(classes) if not (a & forced))
    flags = frozenset((i, j) for i, (b, _) in enumerate(classes)
                      for j, (_, a) in enumerate(classes) if b & a)
    I = Instance(tuple(delta), finals, flags)
    for f in finals:
        for q in delta[f]:
            assert not classes[q][1], 'F-final successor must have empty A subset'
    return I, classes, forced


def absorption_violations(I):
    """Check successors of finals are final and have empty incoming columns."""
    result = []
    for f in sorted(I.final):
        for a, q in enumerate(I.delta[f]):
            if q < 0: continue
            incoming = sorted(p for p, r in I.flags if r == q)
            if q not in I.final or incoming:
                result.append(dict(final=f,letter=I.alphabet[a],successor=q,
                                   successor_final=q in I.final,incoming=incoming))
    return result


def denial_free_decision(I):
    """Exact under totality/no-Bad/absorption guards; otherwise UNKNOWN.

    Requires well-formed Instance conventions and two distinct letters.
    """
    if len(set(I.alphabet)) < 2:
        return dict(status='UNKNOWN',reason='At least two distinct letters required')
    if I.bad or any(q < 0 for row in I.delta for q in row) or absorption_violations(I):
        return dict(status='UNKNOWN',reason='Subclass hypotheses not satisfied')
    diagonal = {p for p, q in I.flags if p == q}
    if I.start in diagonal:
        return dict(status='NO',reason='Initial state has a diagonal flag')
    columns = {q for _, q in I.flags}
    zero = I.final - columns
    queue = deque([I.start])
    parent = {I.start: None}
    target = None
    while queue:
        q = queue.popleft()
        if q in zero:
            target = q
            break
        for a, r in zip(I.alphabet, I.delta[q]):
            if r not in diagonal and r not in parent:
                parent[r] = (q, a)
                queue.append(r)
    if target is None:
        return dict(status='NO',reason='No diagonal-safe path to a zero-column final')
    path = []
    while parent[target] is not None:
        target, a = parent[target]
        path.append(a)
    v = ''.join(reversed(path))
    n = len(v)
    w = '' if n == 0 else v + I.alphabet[0] * n + I.alphabet[1]
    assert witness(I,w) and border_witness(I,w)
    assert sufficient(I,w,n,0)
    assert n <= len(I.delta)-1
    return dict(status='YES',word=w,seed_prefix=v,certified_budget=n,
                word_length=len(w),states=len(I.delta))


def main():
    rng = random.Random(2026090421)
    rows = []
    counts = {'YES':0,'NO':0}
    maximum = 0
    for attempt in range(400):
        k = rng.randrange(2,6)
        constraints = []
        for _ in range(rng.randrange(0,2*k+1)):
            constraints.append((rng.choice(('lower','upper','leq')),
                                rng.randrange(k),rng.randrange(k),rng.randrange(k)))
        I, classes, forced = independent_bridge(k,constraints)
        assert not absorption_violations(I)
        answer = denial_free_decision(I)
        assert answer['status'] in counts
        counts[answer['status']] += 1
        maximum = max(maximum,len(I.delta))
        if answer['status'] == 'NO':
            assert Sandwich(I,0,0).search()['status'] == 'NO'
        rows.append(dict(attempt=attempt,variables=k,constraints=constraints,
                         states=len(I.delta),forced_roots=sorted(forced),answer=answer))
    exclusions = {'five_state_growth':absorption_violations(family(4,3)),
                  'previous_six_state':absorption_violations(BASE)}
    assert all(exclusions.values())
    assert denial_free_decision(family(4,3))['status']=='UNKNOWN'
    out = dict(status='PASS',seed=2026090421,generated_systems=len(rows),
               verdict_counts=counts,maximum_summary_classes=maximum,
               absorption_violations=0,abstract_exclusions=exclusions,rows=rows,
               scope='Independent normalized denial-free NFA implementation; not a rerun of the repository full bridge.',
               proof_status='Written proof; not Lean-checked')
    (ROOT/'results/summary-absorption.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Summary absorption:',len(rows),'normalized systems PASS;',counts,
          '; maximum classes:',maximum)

if __name__=='__main__': main()

"""Exact four-state diagnostic for Q004 source-simple normalization.

Besides literal flagged sources, compute LIVE flags: a flag (p,q) is live only
if some accepted safe run can visit p and later q. Dead flags can be removed
without changing witnesshood. The normalized four-state theorem says every
positive instance has a witness through length four, so this finite class can
exactly falsify either source-simple conjecture.
"""
import itertools
import json
from collections import Counter
from pathlib import Path

from border_lab import Instance, witness, words

ROOT = Path(__file__).resolve().parents[1]
PAIRS = ((0, 1), (0, 2), (1, 2), (2, 1))
WORD_LIST = tuple(words('01', 4))


def reachable(delta, starts):
    seen = set(starts)
    todo = list(starts)
    for p in todo:
        for q in delta[p]:
            if q >= 0 and q not in seen:
                seen.add(q)
                todo.append(q)
    return seen


def reverse_reachable(delta, targets):
    pred = [[] for _ in delta]
    for p, row in enumerate(delta):
        for q in row:
            if q >= 0:
                pred[q].append(p)
    seen = set(targets)
    todo = list(targets)
    for q in todo:
        for p in pred[q]:
            if p not in seen:
                seen.add(p)
                todo.append(p)
    return seen


def live_flags(I):
    """Flags realizable in order on some accepted run (no Bad in this census)."""
    from_start = reachable(I.delta, {I.start})
    to_final = reverse_reachable(I.delta, I.final)
    reach_cache = {p: reachable(I.delta, {p}) for p in range(len(I.delta))}
    return frozenset((p, q) for p, q in I.flags
                     if p in from_start and q in to_final and q in reach_cache[p])


def counts_for_sources(I, w, sources):
    run = I.run(w)
    return {p: run.count(p) for p in sources}


def simple_for_sources(I, w, sources):
    return all(v <= 1 for v in counts_for_sources(I, w, sources).values())


def main():
    total = positive = negative = 0
    literal_simple = live_simple = 0
    live_visit_distribution = Counter()
    live_multiplicity_distribution = Counter()
    max_live_total = max_live_mult = 0

    for transitions in itertools.product((-1, 1, 2, 3), repeat=6):
        delta = tuple(tuple(transitions[2*q:2*q+2]) for q in range(3)) + ((-1, -1),)
        for mask in range(16):
            flags = frozenset(p for bit, p in enumerate(PAIRS) if mask & (1 << bit))
            I = Instance(delta, frozenset({3}), flags)
            total += 1
            ws = [w for w in WORD_LIST if witness(I, w)]
            if not ws:
                negative += 1
                continue
            positive += 1
            literal_sources = {p for p, _ in flags}
            lflags = live_flags(I)
            live_sources = {p for p, _ in lflags}

            if any(simple_for_sources(I, w, literal_sources) for w in ws):
                literal_simple += 1
            if any(simple_for_sources(I, w, live_sources) for w in ws):
                live_simple += 1

            scored = []
            for w in ws:
                counts = counts_for_sources(I, w, live_sources)
                scored.append((sum(counts.values()), max(counts.values(), default=0)))
            best = min(scored)
            live_visit_distribution[best[0]] += 1
            live_multiplicity_distribution[best[1]] += 1
            max_live_total = max(max_live_total, best[0])
            max_live_mult = max(max_live_mult, best[1])

    assert total == 65536 and positive + negative == total
    assert literal_simple == 45426  # catches accidental class-definition drift
    result = {
        'status': 'PASS',
        'instances': total,
        'positive': positive,
        'negative': negative,
        'literal_source_simple_positive': literal_simple,
        'literal_source_simple_counterexamples': positive - literal_simple,
        'live_source_simple_positive': live_simple,
        'live_source_simple_counterexamples': positive - live_simple,
        'max_min_live_source_visits': max_live_total,
        'max_min_live_source_multiplicity': max_live_mult,
        'minimum_live_visit_distribution': dict(sorted(live_visit_distribution.items())),
        'minimum_live_multiplicity_distribution': dict(sorted(live_multiplicity_distribution.items())),
        'scope': ('Exact over the complete normalized four-state terminal class. Dead-flag '
                  'pruning is exact here because such a flag cannot occur in order on any '
                  'accepted run. Survival in this finite class is evidence, not a Q004 proof.'),
    }
    out = ROOT / 'results' / 'source-simple-four-state.json'
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

"""Exact four-state diagnostic for Q004 source-simple normalization.

Besides literal flagged sources, compute ACTIVE flags: a flag (p,q) is active
only if some accepted safe run can visit p and later q. Dead flags can be
removed without changing witnesshood. The normalized four-state theorem says
every positive instance has a witness through length four, so this finite
class can exactly falsify either source-simple conjecture.
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


def active_flags(I):
    # No Bad states occur in this normalized census. A flag can occur at i<=j
    # on an accepted run iff p is start-reachable, q is reachable from p, and
    # q can still reach the terminal final.
    from_start = reachable(I.delta, {I.start})
    to_final = reverse_reachable(I.delta, I.final)
    out = set()
    for p, q in I.flags:
        if p in from_start and q in to_final and q in reachable(I.delta, {p}):
            out.add((p, q))
    return frozenset(out)


def counts_for_sources(I, w, sources):
    run = I.run(w)
    return {p: run.count(p) for p in sources}


def simple_for_sources(I, w, sources):
    return all(v <= 1 for v in counts_for_sources(I, w, sources).values())


def main():
    total = positive = negative = 0
    literal_simple = active_simple = 0
    literal_counterexamples = []
    active_counterexamples = []
    active_visit_distribution = Counter()
    active_multiplicity_distribution = Counter()
    max_active_total = max_active_mult = 0
    active_extremal = None

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
            aflags = active_flags(I)
            active_sources = {p for p, _ in aflags}

            ls = [w for w in ws if simple_for_sources(I, w, literal_sources)]
            if ls:
                literal_simple += 1
            elif len(literal_counterexamples) < 8:
                literal_counterexamples.append({
                    'delta': delta, 'flags': sorted(flags), 'active_flags': sorted(aflags),
                    'witnesses_through_4': ws,
                    'counts': {w: counts_for_sources(I, w, literal_sources) for w in ws},
                })

            ac = [w for w in ws if simple_for_sources(I, w, active_sources)]
            if ac:
                active_simple += 1
            elif len(active_counterexamples) < 8:
                active_counterexamples.append({
                    'delta': delta, 'flags': sorted(flags), 'active_flags': sorted(aflags),
                    'witnesses_through_4': ws,
                    'counts': {w: counts_for_sources(I, w, active_sources) for w in ws},
                })

            scored = []
            for w in ws:
                counts = counts_for_sources(I, w, active_sources)
                scored.append((sum(counts.values()), max(counts.values(), default=0), len(w), w, counts))
            best = min(scored)
            active_visit_distribution[best[0]] += 1
            active_multiplicity_distribution[best[1]] += 1
            if (best[0], best[1]) > (max_active_total, max_active_mult):
                max_active_total, max_active_mult = best[0], best[1]
                active_extremal = {'delta': delta, 'flags': sorted(flags),
                                   'active_flags': sorted(aflags), 'word': best[3],
                                   'counts': best[4], 'length': best[2]}

    assert total == 65536 and positive + negative == total
    result = {
        'status': 'PASS', 'instances': total, 'positive': positive, 'negative': negative,
        'literal_source_simple_positive': literal_simple,
        'literal_source_simple_counterexamples': positive - literal_simple,
        'literal_counterexample_samples': literal_counterexamples,
        'active_source_simple_positive': active_simple,
        'active_source_simple_counterexamples': positive - active_simple,
        'active_counterexample_samples': active_counterexamples,
        'max_min_active_source_visits': max_active_total,
        'max_min_active_source_multiplicity': max_active_mult,
        'minimum_active_visit_distribution': dict(sorted(active_visit_distribution.items())),
        'minimum_active_multiplicity_distribution': dict(sorted(active_multiplicity_distribution.items())),
        'active_extremal': active_extremal,
        'scope': ('Exact over the complete normalized four-state terminal class. Active-flag '
                  'normalization is exact here because dead flags cannot occur in any i<=j '
                  'pair on a safe accepted run. Finite-class survival is not a general theorem.'),
    }
    out = ROOT / 'results' / 'source-simple-four-state.json'
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

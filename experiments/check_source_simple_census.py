"""Exact four-state diagnostic for Q004 source-simple normalization.

The normalized four-state terminal theorem establishes that every positive
instance has a witness of length at most four. We exhaust those words and ask
whether at least one witness visits each flagged source state at most once.
A counterexample would refute source-simple normalization outright at four
states; absence is finite-class evidence only, not a general theorem.
"""
import itertools
import json
from collections import Counter
from pathlib import Path

from border_lab import Instance, witness, words

ROOT = Path(__file__).resolve().parents[1]
PAIRS = ((0, 1), (0, 2), (1, 2), (2, 1))
WORD_LIST = tuple(words('01', 4))


def source_counts(I, w):
    run = I.run(w)
    sources = {p for p, _ in I.flags}
    return {p: run.count(p) for p in sources}


def source_simple(I, w):
    return all(v <= 1 for v in source_counts(I, w).values())


def main():
    total = positive = negative = source_simple_positive = 0
    max_min_total_visits = 0
    max_min_max_multiplicity = 0
    visit_distribution = Counter()
    multiplicity_distribution = Counter()
    extremal = None
    counterexamples = []

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
            simple = [w for w in ws if source_simple(I, w)]
            if simple:
                source_simple_positive += 1
            else:
                counterexamples.append({
                    'delta': delta,
                    'flags': sorted(flags),
                    'witnesses_through_4': ws,
                    'source_counts': {w: source_counts(I, w) for w in ws},
                })

            scored = []
            for w in ws:
                counts = source_counts(I, w)
                total_visits = sum(counts.values())
                max_mult = max(counts.values(), default=0)
                scored.append((total_visits, max_mult, len(w), w, counts))
            best = min(scored)
            visit_distribution[best[0]] += 1
            multiplicity_distribution[best[1]] += 1
            if (best[0] > max_min_total_visits or
                (best[0] == max_min_total_visits and best[1] > max_min_max_multiplicity)):
                max_min_total_visits = best[0]
                max_min_max_multiplicity = best[1]
                extremal = {'delta': delta, 'flags': sorted(flags), 'word': best[3],
                            'counts': best[4], 'length': best[2]}

    assert total == 65536
    assert positive + negative == total
    result = {
        'status': 'PASS',
        'instances': total,
        'positive': positive,
        'negative': negative,
        'source_simple_positive': source_simple_positive,
        'source_simple_counterexamples': len(counterexamples),
        'first_counterexample': counterexamples[0] if counterexamples else None,
        'max_min_total_source_visits': max_min_total_visits,
        'max_min_source_multiplicity': max_min_max_multiplicity,
        'minimum_total_visit_distribution': dict(sorted(visit_distribution.items())),
        'minimum_max_multiplicity_distribution': dict(sorted(multiplicity_distribution.items())),
        'extremal': extremal,
        'scope': ('Exact over the complete normalized four-state terminal class because the '
                  'existing theorem guarantees a witness through length four when positive; '
                  'absence of a counterexample in this finite class is not a general Q004 proof.'),
    }
    out = ROOT / 'results' / 'source-simple-four-state.json'
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

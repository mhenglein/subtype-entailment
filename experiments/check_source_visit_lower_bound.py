"""Reproduce the modular-family lower bound on flagged-source visits for Q004.

The all-length witness-language proof is C046.  This checker independently
counts flagged-source occurrences in the displayed shortest witnesses and
records the resulting Q004 calibration.  Large-m rows evaluate the proved
closed form; they are not exhaustive witness searches.
"""
import json
from pathlib import Path
from modular_sync_family import make_family, word_from_counts, predicted_witness
from border_lab import witness

ROOT = Path(__file__).resolve().parents[1]


def source_visits(I, w):
    sources = {p for p, _ in I.flags}
    run = I.run(w)
    return sum(q in sources for q in run)


def row(periods):
    F = make_family(periods)
    r = len(periods)
    P = F.common_period
    w = word_from_counts((P,) * r)
    assert witness(F.instance, w) and predicted_witness(F, w)
    actual = source_visits(F.instance, w)
    expected = (r - 1) * (P + 1)
    assert actual == expected == F.exact_budget
    # C046 proves every witness has common block length N a positive multiple
    # of P, hence this displayed value is the all-witness minimum.
    return {
        'periods': list(periods), 'states': len(F.instance.delta), 'lcm': P,
        'minimum_source_visits_from_C046': expected,
        'shortest_witness_length': len(w),
        'direct_shortest_witness_source_visits': actual,
    }


def main():
    examples = [row((2,3)), row((3,4)), row((2,3,5)), row((2,3,5,7))]
    growth = []
    for m in range(3, 13):
        F = make_family(range(1, m + 1))
        k = len(F.instance.delta)
        P = F.common_period
        minimum = (m - 1) * (P + 1)
        assert minimum == F.exact_budget
        assert P * (m + 1) >= 2 ** m
        growth.append({'m': m, 'states': k, 'lcm': P,
                       'minimum_source_visits_from_C046': minimum,
                       'elementary_lower_bound': 2 ** (m - 1)})
    result = {
        'status': 'PASS',
        'examples': examples,
        'growth': growth,
        'theorem': ('For the C046 r-block modular family, the minimum number of '
                    'flagged-source run positions among all witnesses is exactly '
                    '(r-1)(lcm(p_1,...,p_r)+1).'),
        'asymptotic_consequence': ('For periods 1..m and k=(m+1)(m+2)/2 states, '
                                   'every witness has at least 2^(m-1) flagged-source '
                                   'visits; therefore every universal Q004 bound R(k) '
                                   'is 2^Omega(sqrt(k)) on an infinite subsequence.'),
        'proof_status': ('Source-visit count is a direct corollary of C046 written '
                         'all-length witness characterization; checker validates '
                         'displayed words/counts. Not newly Lean-checked.'),
    }
    path = ROOT / 'results' / 'source-visit-lower-bound.json'
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

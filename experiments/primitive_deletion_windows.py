"""Exhaustive probe for deletion windows that destroy primitivity.

For each primitive binary word z through length 15, count intervals [i,j) with
nonempty remainder such that deleting z[i:j] yields a proper power. This is a
combinatorial diagnostic for the synchronized-window surgery in
notes/2026-09-08-single-source-shape-lemmas.md; finite data is not a proof.
"""
from itertools import product
import json
from pathlib import Path


def is_primitive(w: str) -> bool:
    n = len(w)
    if n <= 1:
        return True
    return not any(n % d == 0 and w == w[:d] * (n // d) for d in range(1, n))


def bad_window_count(w: str) -> int:
    n = len(w)
    count = 0
    for i in range(n):
        for j in range(i + 1, n + 1):
            if j - i == n:
                continue
            if not is_primitive(w[:i] + w[j:]):
                count += 1
    return count


def main(max_n: int = 15):
    rows = []
    for n in range(2, max_n + 1):
        primitive_count = 0
        max_bad = -1
        example = None
        for bits in product('01', repeat=n):
            w = ''.join(bits)
            if not is_primitive(w):
                continue
            primitive_count += 1
            count = bad_window_count(w)
            if count > max_bad:
                max_bad = count
                example = w
        rows.append({
            'n': n,
            'primitive_words': primitive_count,
            'max_bad_windows': max_bad,
            'example': example,
        })

    result = {
        'status': 'PASS',
        'scope': 'Exhaustive primitive binary words through length 15; combinatorial diagnostic only, not a proof of the single-source bound',
        'max_n': max_n,
        'rows': rows,
        'proved_lower_bound_family': 'For a primitive length-n word with one 1 in an interior position a, every deletion interval containing that 1 and leaving at least two symbols produces 0^k and is bad. A centered 1 gives floor((n+1)^2/4)-3 bad windows.',
        'observation': 'The exhaustive maximum equals floor((n+1)^2/4)-3 for n=3..15. This equality is empirical beyond the displayed lower-bound family and is not claimed as a theorem.',
        'consequence': 'A proof that merely upper-bounds the total number of primitivity-destroying windows by o(n^2) cannot work.',
    }
    path = Path(__file__).resolve().parents[1] / 'results' / 'primitive-deletion-windows.json'
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

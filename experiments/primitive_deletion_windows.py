"""Exhaustive probe for deletion windows that destroy primitivity.

For each primitive binary word z, count intervals [i,j) with 0 <= i < j <= |z|
and nonempty remainder such that deleting z[i:j] yields a proper power.
This is a combinatorial diagnostic for the synchronized-window surgery in
notes/2026-09-08-single-source-shape-lemmas.md; finite data is not a proof.
"""
from itertools import product
import json
from pathlib import Path


def is_primitive(w: str) -> bool:
    n = len(w)
    if n <= 1:
        return True
    for d in range(1, n):
        if n % d == 0 and w == w[:d] * (n // d):
            return False
    return True


def bad_windows(w: str):
    n = len(w)
    out = []
    for i in range(n):
        for j in range(i + 1, n + 1):
            if j - i == n:
                continue
            v = w[:i] + w[j:]
            if not is_primitive(v):
                # Record shortest root length of the remainder as a diagnostic.
                root = len(v)
                for d in range(1, len(v)):
                    if len(v) % d == 0 and v == v[:d] * (len(v) // d):
                        root = d
                        break
                out.append((i, j, len(v), root))
    return out


def main(max_n=15):
    rows = []
    global_examples = []
    for n in range(2, max_n + 1):
        primitive_count = 0
        max_bad = -1
        max_by_length = -1
        examples = []
        for bits in product('01', repeat=n):
            w = ''.join(bits)
            if not is_primitive(w):
                continue
            primitive_count += 1
            bad = bad_windows(w)
            count = len(bad)
            lengths = len({j-i for i,j,_,_ in bad})
            if count > max_bad:
                max_bad = count
                max_by_length = lengths
                examples = [(w, bad[:12])]
            elif count == max_bad and len(examples) < 4:
                examples.append((w, bad[:12]))
        rows.append({
            'n': n,
            'primitive_words': primitive_count,
            'max_bad_windows': max_bad,
            'max_bad_window_lengths_on_first_extremal': max_by_length,
            'ratio_to_n2': max_bad / (n*n),
            'examples': [{'word': w, 'bad_windows_sample': b} for w,b in examples],
        })
        global_examples.extend((n,w,b) for w,b in examples[:1])
    result = {
        'status': 'PASS',
        'scope': 'exhaustive primitive binary words through stated length; diagnostic only',
        'max_n': max_n,
        'rows': rows,
        'candidate_observation': 'compare max_bad_windows with polynomial functions of n; no theorem asserted',
    }
    path = Path(__file__).resolve().parents[1] / 'results' / 'primitive-deletion-windows.json'
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

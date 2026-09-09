"""Equality-compatible deletion masks for overlapping factor occurrences.

These are certificates for a supplied word and selected factor equalities,
not a witness-existence decision or a no-new-border theorem.
"""
from border_lab import Instance
from collective_transport import validate


def _positions(n, values, allow_end=False):
    values = frozenset(values)
    if any(type(v) is not int or not 0 <= v < n + int(allow_end) for v in values):
        raise ValueError('Invalid position')
    return values


def _agreements(n, agreements):
    result = tuple(tuple(a) for a in agreements)
    if any(len(a) != 3 or any(type(v) is not int for v in a)
           or not (0 <= a[0] < a[1] <= n and 0 <= a[2] <= n-a[1])
           for a in result):
        raise ValueError('Expected ordered starts and a valid common length')
    return result


def alignment_closure(n, agreements, seeds):
    """Least deletion mask containing seeds and respecting every alignment.

    For (a,b,r), deletion of a+t is equivalent to deletion of b+t, 0<=t<r.
    Minimality concerns these explicit mask constraints, not every possible
    accidental equality of the surviving strings.
    """
    if type(n) is not int or n < 0:
        raise ValueError('Length must be a nonnegative integer')
    agreements = _agreements(n, agreements)
    seeds = _positions(n, seeds)
    parent = list(range(n))

    def find(p):
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p

    for a, b, r in agreements:
        for t in range(r):
            x, y = find(a+t), find(b+t)
            if x != y:
                parent[y] = x
    marked = {find(p) for p in seeds}
    return frozenset(p for p in range(n) if find(p) in marked)


def intervals(mask):
    out = []
    for p in sorted(mask):
        if out and out[-1][1] == p:
            out[-1] = (out[-1][0], p+1)
        else:
            out.append((p, p+1))
    return tuple(out)


def survivor(word, start, end, mask):
    return ''.join(word[p] for p in range(start, end) if p not in mask)


def certify(I, word, agreements, seeds, protected_letters=(), protected_cuts=()):
    """Check acceptance, selected equalities, and their endpoint-state colours.

    The least compatible mask is tested, not an exhaustive search for every
    possible deletion. NOT_CERTIFIED never means that no shorter witness exists.
    """
    validate(I)
    if not I.admissible(word):
        raise ValueError('An admissible original word is required')
    n = len(word)
    agreements = _agreements(n, agreements)
    protected_letters = _positions(n, protected_letters)
    protected_cuts = _positions(n, protected_cuts, allow_end=True)
    if any(word[a:a+r] != word[b:b+r] for a, b, r in agreements):
        raise ValueError('The supplied factor equality is false')
    mask = alignment_closure(n, agreements, seeds)
    if not mask:
        return {'status': 'NOT_CERTIFIED', 'reason': 'no strict shortening'}
    if mask & protected_letters:
        return {'status': 'NOT_CERTIFIED', 'reason': 'protected letter'}
    runs = intervals(mask)
    old = I.run(word)
    if any(old[lo] != old[hi] for lo, hi in runs):
        return {'status': 'NOT_CERTIFIED', 'reason': 'not a union of state loops'}
    cuts = set(protected_cuts)
    for a, b, r in agreements:
        cuts.update((a, b, a+r, b+r))
    if any(lo < cut < hi for lo, hi in runs for cut in cuts):
        return {'status': 'NOT_CERTIFIED', 'reason': 'a protected cut is inside a deletion'}
    offset = [0]
    for p in range(n):
        offset.append(offset[-1] + int(p not in mask))
    if any(offset[a] >= offset[b] for a, b, r in agreements):
        return {'status': 'NOT_CERTIFIED', 'reason': 'comparison starts collapse'}
    result = survivor(word, 0, n, mask)
    new = I.run(result)
    assert I.admissible(result) and len(result) < n
    assert all(new[offset[p]] == old[p] for p in cuts)
    images = []
    for a, b, r in agreements:
        x, y = result[offset[a]:offset[a+r]], result[offset[b]:offset[b+r]]
        assert x == y
        images.append((offset[a], offset[b], len(x)))
    return {'status': 'CERTIFIED', 'word': result, 'deleted': sorted(mask),
            'intervals': runs, 'images': images, 'preserved_cuts': sorted(cuts)}


def four_block_instance():
    """Six states; start has no incoming transition; final is terminal."""
    return Instance(((1,-1),(1,2),(2,3),(3,4),(4,5),(-1,-1)), frozenset({5}))

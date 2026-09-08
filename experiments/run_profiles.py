"""All-instance run-length normalization for binary BorderAvoid.

No markers are added. Use the final letter of a nonempty word as its marker.
The transformation preserves the EXACT full state-pair agreement profile and
visited states. A marker budget is not a global witness bound.
"""
from dataclasses import dataclass
from math import lcm
from typing import FrozenSet, Tuple

from border_lab import Instance


def validate_binary(I: Instance, terminal: bool = True) -> None:
    k = len(I.delta)
    if not k or I.alphabet != '01' or not 0 <= I.start < k:
        raise ValueError('A nonempty binary instance with a valid start is required')
    if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < k for q in row) for row in I.delta):
        raise ValueError('Invalid binary transition table')
    if not (set(I.final) | set(I.bad)) <= set(range(k)):
        raise ValueError('Invalid final/Bad annotation')
    if any(p not in range(k) or q not in range(k) for p, q in I.flags):
        raise ValueError('Invalid flag endpoint')
    if terminal and any(q >= 0 for f in I.final for q in I.delta[f]):
        raise ValueError('Accepting states must be terminal')


@dataclass(frozen=True)
class UnaryOrbit:
    """Completed deterministic data transition; sink is the extra index k."""
    table: Tuple[int, ...]
    period: int
    cutoff: int
    difference_cutoff: int

    def path(self, p: int):
        order, indices = [], {}
        while p not in indices:
            indices[p] = len(order)
            order.append(p)
            p = self.table[p]
        return order, indices[p]

    def at(self, p: int, n: int) -> int:
        if n < 0:
            raise ValueError('Unary exponent must be nonnegative')
        path, begin = self.path(p)
        return path[n] if n < len(path) else path[begin+(n-begin) % (len(path)-begin)]

    def visited(self, p: int, n: int) -> FrozenSet[int]:
        path, _ = self.path(p)
        return frozenset(path[:min(n+1, len(path))])


def unary_orbit(I: Instance, marker: str) -> UnaryOrbit:
    validate_binary(I, terminal=False)
    if marker not in ('0', '1'):
        raise ValueError('Marker must be one bit')
    k = len(I.delta)
    data = 1-int(marker)
    table = tuple(row[data] if row[data] >= 0 else k for row in I.delta)+(k,)
    period = 1
    for start in range(k+1):
        positions, q = {}, start
        while q not in positions:
            positions[q] = len(positions)
            q = table[q]
        period = lcm(period, len(positions)-positions[q])
    return UnaryOrbit(table, period, (k+1)**2, k+1)


def split_runs(word: str, marker: str):
    if any(a not in '01' for a in word) or marker not in ('0', '1'):
        raise ValueError('Binary word and marker required')
    if not word or not word.endswith(marker):
        raise ValueError('A nonempty word ending in the chosen marker is required')
    return tuple(map(len, word[:-1].split(marker)))


def join_runs(lengths, marker: str) -> str:
    lengths = tuple(lengths)
    if marker not in ('0', '1') or any(type(n) is not int or n < 0 for n in lengths):
        raise ValueError('Nonnegative integer lengths and binary marker required')
    return ''.join(str(1-int(marker))*n+marker for n in lengths)


def compress_lengths(lengths, orbit: UnaryOrbit):
    """Canonical contraction preserving residues, order and all short gaps.

    Anchor every value <=T exactly. Beyond T, contract an adjacent gap g>=h
    to h+((g-h) mod P); retain gaps g<h. No coordinate increases.
    This works on integers without expanding the data runs.
    """
    ns = tuple(lengths)
    if any(type(n) is not int or n < 0 for n in ns):
        raise ValueError('Run lengths must be nonnegative integers')
    T, h, P = orbit.cutoff, orbit.difference_cutoff, orbit.period
    mapping = {x:x for x in set(ns) if x <= T}
    old, new = T, T
    for x in sorted(set(ns)-set(mapping)):
        gap = x-old
        step = gap if gap < h else h+(gap-h) % P
        new += step
        mapping[x] = new
        old = x
    result = tuple(mapping[x] for x in ns)
    assert all(y <= x and (x-y) % P == 0 for x, y in zip(ns, result))
    assert max(result, default=0) <= T+len(set(ns))*(h+P-1)
    return result


def pair_signature(n: int, m: int, orbit: UnaryOrbit):
    """Finite orbit information sufficient to determine every equal-tail hit."""
    sign = (n > m)-(n < m)
    gap = abs(n-m)
    gtype = ('short', gap) if gap < orbit.difference_cutoff else ('long', gap % orbit.period)
    small = min(n,m)
    stype = ('short', small) if small < orbit.cutoff else ('long',)
    return sign, gtype, stype


def equal_tail_pairs(orbit: UnaryOrbit, p: int, n: int, q: int, m: int):
    """Exact set of state pairs at equal unary-tail depths, without expansion.

    Iterate the product orbit after skipping the excess of the longer run.
    It has at most (k+1)^2 states; stop at first repeated pair or min(n,m).
    """
    if min(n,m) < 0:
        raise ValueError('Nonnegative lengths required')
    left = orbit.at(p,max(0,n-m))
    right = orbit.at(q,max(0,m-n))
    seen, t = set(), 0
    while (left,right) not in seen and t <= min(n,m):
        seen.add((left,right))
        left, right = orbit.table[left], orbit.table[right]
        t += 1
    return frozenset(seen)


def numeric_profile(I: Instance, lengths, marker: str):
    """Exact full agreement profile of an accepted run-vector, no word expansion.

    This ignores flags and Bad on purpose: the returned visited set and full
    profile determine witnesshood for EVERY annotation on this fixed DFA.
    Returns None if the vector is not an accepted candidate.
    """
    orbit = unary_orbit(I,marker)
    ns = tuple(lengths)
    if not ns or any(type(n) is not int or n < 0 for n in ns):
        raise ValueError('A nonempty tuple of nonnegative lengths is required')
    starts, visited = [], {I.start}
    q, k = I.start, len(I.delta)
    for n in ns:
        starts.append(q)
        visited.update(orbit.visited(q,n))
        end = orbit.at(q,n)
        if end == k:
            return None
        q = I.delta[end][int(marker)]
        if q < 0:
            return None
        visited.add(q)
    if q not in I.final:
        return None
    profile = {(p,p) for p in visited} | {(p,q) for p in visited}
    r = len(ns)
    for i in range(r):
        for j in range(i+1,r):
            if all(ns[i+h] == ns[j+h] for h in range(1,r-j)):
                profile.update(equal_tail_pairs(orbit,starts[i],ns[i],starts[j],ns[j]))
    return dict(endpoint=q, visited=frozenset(visited), profile=frozenset(profile),
                starts=tuple(starts), period=orbit.period)


def normalize_candidate(I: Instance, word: str):
    """Preserve acceptance, visited set and full profile of ANY accepted word."""
    validate_binary(I, terminal=False)
    if not I.run(word) or I.run(word)[-1] not in I.final:
        raise ValueError('An accepted candidate word is required')
    if word == '':
        return dict(word='', lengths=(), old_lengths=(), marker=None)
    marker = word[-1]
    ns = split_runs(word,marker)
    orbit = unary_orbit(I,marker)
    small = compress_lengths(ns,orbit)
    out = join_runs(small,marker)
    before = numeric_profile(I,ns,marker)
    after = numeric_profile(I,small,marker)
    assert before is not None and after is not None
    for key in ('endpoint','visited','profile','starts'):
        assert before[key] == after[key]
    r, d = len(ns), len(set(ns))
    bound = r*(orbit.cutoff+d*(orbit.difference_cutoff+orbit.period-1)+1)
    assert len(out) <= bound and len(out) <= len(word)
    return dict(word=out, old_lengths=ns, lengths=small, marker=marker,
                period=orbit.period, threshold=orbit.cutoff,
                difference_cutoff=orbit.difference_cutoff,
                distinct_lengths=d, bound=bound)


def last_bit_slice(I: Instance, final: int, marker: str) -> Instance:
    """Exact word-preserving slice; no new states, symbols or delimiters.

    Other terminal finals are made nonaccepting. Delete only wrong-labelled
    transitions into the chosen final. All annotations are left unchanged.
    The empty word, when accepted, is handled separately by a caller.
    """
    validate_binary(I)
    if final not in I.final or marker not in ('0','1'):
        raise ValueError('Choose an original final and a binary marker')
    table = tuple(tuple(-1 if q == final and a != int(marker) else q
                        for a,q in enumerate(row)) for row in I.delta)
    return Instance(table,frozenset({final}),I.flags,I.bad,I.start,I.alphabet)


def run_length_bound(k: int, markers: int) -> int:
    """A computable uniform bound conditional on a marker-count budget."""
    if type(k) is not int or type(markers) is not int or k < 1 or markers < 0:
        raise ValueError('Positive state count and nonnegative marker count required')
    P = 1
    for n in range(1,k+1):
        P = lcm(P,n)
    return markers*((k+1)**2+markers*(k+P)+1)


def encode_zero_tail(word: str) -> str:
    if any(a not in '01' for a in word):
        raise ValueError('Binary word required')
    return ''.join(a+'0' for a in word)


def decode_zero_tail(word: str):
    if any(a not in '01' for a in word) or len(word)%2 or any(word[i]!='0' for i in range(1,len(word),2)):
        return None
    return word[::2]


def bounded_run_encoding(I: Instance) -> Instance:
    """Exact linear-size reduction to words in (00|10)*, without appending #.

    Original states 0..k-1 occur only at even boundaries. Helper k+q has
    only the 0 edge to q. Flags and Bad remain on original state copies.
    All nonempty accepted words end in 0 and have no consecutive 1s.
    Terminality of accepting states is preserved, when present in the input.
    """
    validate_binary(I,terminal=False)
    k=len(I.delta)
    boundary=tuple(tuple(k+q if q>=0 else -1 for q in row) for row in I.delta)
    helpers=tuple((q,-1) for q in range(k))
    return Instance(boundary+helpers,I.final,I.flags,I.bad,I.start,I.alphabet)


def final_symbol_frontier_decision(I: Instance, limits=None):
    """Sound extension of C056 via all final-state/last-bit slices.

    NO is returned only when every exact partition slice is certified empty.
    Marker cycles reachable from targets are still an unresolved case.
    """
    from target_frontier import Limits, target_frontier_decision
    from border_lab import witness,border_witness
    validate_binary(I)
    if limits is None:
        limits=Limits()
    if witness(I,''):
        return dict(status='YES',word='',reason='Empty witness',slices=[])
    unknown=False;reports=[]
    for f in sorted(I.final):
        for marker in '01':
            J=last_bit_slice(I,f,marker)
            if marker=='1':
                J=Instance(tuple((r[1],r[0]) for r in J.delta),J.final,J.flags,J.bad,J.start,J.alphabet)
            out=target_frontier_decision(J,limits)
            reports.append(dict(final=f,marker=marker,result=out))
            if out['status']=='YES':
                word=out['word']
                if marker=='1':word=word.translate(str.maketrans('01','10'))
                assert witness(I,word) and border_witness(I,word)
                return dict(status='YES',word=word,slices=reports)
            if out['status']!='NO':unknown=True
    return dict(status='UNKNOWN' if unknown else 'NO',slices=reports,
                reason='At least one slice unresolved' if unknown else 'Every exact last-bit slice is empty')

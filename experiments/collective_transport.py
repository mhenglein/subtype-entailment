"""Finite cyclic certificates for collective relocation of suffix flags.

A backward proof strictly decreases source-cut position at every recursive
step. The forward proof is a pair-graph cut. Both are sound sufficient checks;
neither is advertised as a completeness theorem for witness existence.
"""
from collections import deque
from itertools import combinations

from border_lab import Instance, witness, border_witness
def validate(I):
    """Validate the exact binary terminal model; no finite-tree substitution."""
    k = len(I.delta)
    if k < 1 or I.alphabet != '01' or type(I.start) is not int or not 0 <= I.start < k:
        raise ValueError('A nonempty binary automaton with a valid start is required')
    if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < k for q in row)
           for row in I.delta):
        raise ValueError('Invalid partial transition table')
    if any(type(q) is not int or not 0 <= q < k for q in I.final | I.bad):
        raise ValueError('Invalid final/Bad state')
    if any(len(g) != 2 or any(type(q) is not int or not 0 <= q < k for q in g)
           for g in I.flags):
        raise ValueError('Invalid flag')
    if any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        raise ValueError('Accepting states must be terminal')


def pair_graph(I):
    """Possible distinct-state synchronized comparisons ending at a final."""
    vertices = {(p, q) for p in range(len(I.delta))
                for q in range(len(I.delta)) if p != q and p not in I.final}
    edges = {v: [] for v in vertices}
    for p, q in vertices:
        for a in range(2):
            dest = (I.delta[p][a], I.delta[q][a])
            if dest in vertices:
                edges[p, q].append((a, dest))
    return vertices, edges


def backward_closure(I, flags=None):
    """Greatest guarded predecessor closure; additional flags imply old ones.

    New (r,s) needs r!=start, one common incoming LETTER at both states, and
    every predecessor pair in the closure. Arbitrarily many incoming states
    and cyclic proof graphs are allowed. The source position is the rank.
    """
    validate(I)
    G = set(I.flags if flags is None else flags)
    V, _ = pair_graph(I)
    inc = [[] for _ in I.delta]
    for p, row in enumerate(I.delta):
        for a, q in enumerate(row):
            if q >= 0:
                inc[q].append((p, a))
    rules = {}
    for r, s in V-G:
        if r == I.start or not inc[r] or not inc[s]:
            continue
        letters = {a for p, a in inc[r]} | {a for p, a in inc[s]}
        if len(letters) != 1:
            continue
        rules[r, s] = frozenset((p, q) for p, a in inc[r] for q, b in inc[s])
    S = G | set(rules)
    while True:
        remove = {v for v in S-G if not rules[v] <= S}
        if not remove:
            break
        S -= remove
    return frozenset(S), {v: rules[v] for v in S-G}


def forward_covered(I, G, H):
    """Every G-rooted terminal pair path meets H, at zero or later offset."""
    V, edges = pair_graph(I)
    H = set(H)
    # Diagonal failure is independent of the proper-gap argument.
    if {p for p, q in G if p == q} - {p for p, q in H if p == q}:
        return False
    avoid = {v for v in V-H if v[1] in I.final}
    back = {v: [] for v in V}
    for v, row in edges.items():
        for a, t in row:
            back[t].append(v)
    todo = deque(avoid)
    while todo:
        v = todo.popleft()
        for p in back[v]:
            if p not in H and p not in avoid:
                avoid.add(p)
                todo.append(p)
    return not (set(G) & avoid)


def verify_rewrite(I, H):
    """Independently decidable proof gate; False means no certificate."""
    validate(I)
    H = frozenset(tuple(v) for v in H)
    if any(len(v) != 2 or any(type(p) is not int or not 0 <= p < len(I.delta)
                             for p in v) for v in H):
        return False
    B, rules = backward_closure(I)
    return H <= B and forward_covered(I, I.flags, H)


def rewrite(I, H):
    H = frozenset(tuple(v) for v in H)
    if not verify_rewrite(I, H):
        raise ValueError('No guarded backward / forward cover certificate')
    return Instance(I.delta, I.final, H, I.bad, I.start, I.alphabet)


def gap_set(I, word):
    """Literal independent specification; positive gaps, including empty tails."""
    if not I.admissible(word):
        return frozenset()
    c = I.run(word)
    return frozenset(j-i for i in range(len(word)+1) for j in range(i+1, len(word)+1)
                     if (c[i],c[j]) in I.flags and word[i:].startswith(word[j:]))


def variants(I, max_variants=100000):
    """All presentations admitted by this finite certificate (or cap).

    The cap counts candidate sets, not just successful presentations.
    """
    if max_variants is not None and (type(max_variants) is not int or max_variants < 1):
        raise ValueError('max_variants must be positive or None')
    B, _ = backward_closure(I)
    mandatory = {p for p in I.flags if p[0] == p[1]}
    allowed = sorted(B-mandatory)
    checked = 0
    for n in range(len(allowed)+1):
        for subset in combinations(allowed,n):
            if max_variants is not None and checked >= max_variants:
                yield {'status':'UNKNOWN','reason':'candidate presentation cap','checked':checked},None
                return
            checked += 1
            H = frozenset(set(subset)|mandatory)
            if forward_covered(I,I.flags,H):
                yield {'status':'CERTIFIED','checked':checked,'flags':sorted(H)},rewrite(I,H)


def barrier():
    return Instance(((1,2),(1,2),(3,-1),(3,4),(5,2),(-1,-1)),frozenset({5}),
                    frozenset({(0,2),(0,3),(1,2)}))


def transported_barrier():
    return rewrite(barrier(), {(0,2),(0,3),(1,3)})


if __name__ == '__main__':
    from lastflag_spectrum import decide
    I = barrier()
    print('Backward closure:', sorted(backward_closure(I)[0]))
    J = transported_barrier()
    print('Rewrite:', sorted(J.flags))
    print('Decision:', decide(J))

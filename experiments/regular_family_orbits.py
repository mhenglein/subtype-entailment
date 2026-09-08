"""Exact regular-family safety via shared-word orbit products (A017).

Question: is EVERY word accepted by D a witness of I? This is not the
existential BorderAvoid question. With both caps None the algorithm terminates.
The explicit BFS implementation uses potentially exponential space; the
accompanying implicit-graph proof, not this implementation, gives PSPACE.
Standard library only. See notes/2026-09-07-regular-family-complexity.md.
"""
from collections import deque
from dataclasses import dataclass, replace
from typing import Optional

from border_lab import Instance, witness, border_witness


def validate_binary(I: Instance) -> None:
    n = len(I.delta)
    if I.alphabet != '01' or not n or type(I.start) is not int or not 0 <= I.start < n:
        raise ValueError('Expected a nonempty binary DFA with a valid start')
    if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < n for q in row)
           for row in I.delta):
        raise ValueError('Transitions must be binary rows with targets -1..n-1')
    if any(type(q) is not int or not 0 <= q < n for q in I.final | I.bad):
        raise ValueError('Invalid final/Bad state')
    if any(len(pair) != 2 or any(type(q) is not int or not 0 <= q < n for q in pair)
           for pair in I.flags):
        raise ValueError('Invalid flag')


def _word(parent, node):
    out = []
    while parent[node] is not None:
        prev, label = parent[node]
        out.append(label)
        node = prev
    return ''.join(reversed(out))


def _bad_member(I, D, word, **extra):
    if not D.admissible(word) or witness(I, word) or border_witness(I, word):
        raise AssertionError('Invalid counterexample returned by orbit search')
    return dict(status='COUNTEREXAMPLE', word=word, **extra)


def _boundary_check(I, D):
    initial = (I.start if I.start not in I.bad else -1, D.start,
               (I.start, I.start) in I.flags)
    todo = deque([initial]); parent = {initial: None}; member = None
    while todo:
        node = todo.popleft(); p, d, diag = node
        if d in D.final:
            if p < 0 or p not in I.final or diag:
                return _bad_member(I, D, _word(parent, node),
                                   reason='Inadmissible member or flagged diagonal'), None
            if member is None:
                member = _word(parent, node)
        for a, target_d in enumerate(D.delta[d]):
            if target_d < 0:
                continue
            q = I.delta[p][a] if p >= 0 else -1
            if q in I.bad:
                q = -1
            nxt = (q, target_d, diag or (q >= 0 and (q, q) in I.flags))
            if nxt not in parent:
                parent[nxt] = (node, str(a)); todo.append(nxt)
    if member is None:
        return dict(status='REGULAR_FAMILY_VALID', inhabited=False,
                    reason='Empty domain'), None
    return None, member


def _live_product(I, D):
    start = (I.start, D.start)
    ids = {start: 0}; pairs = [start]; heads = ['']; rows = []
    for idx, (p, d) in enumerate(pairs):
        row = []
        for a in (0, 1):
            q, r = I.delta[p][a], D.delta[d][a]
            if q < 0 or q in I.bad or r < 0:
                row.append(-1); continue
            pair = (q, r)
            if pair not in ids:
                ids[pair] = len(pairs); pairs.append(pair)
                heads.append(heads[idx] + str(a))
            row.append(ids[pair])
        rows.append(tuple(row))
    finals = {j for j, (p, d) in enumerate(pairs) if p in I.final and d in D.final}
    predecessors = [[] for _ in pairs]
    for p, row in enumerate(rows):
        for q in row:
            if q >= 0:
                predecessors[q].append(p)
    live = set(finals); todo = list(finals)
    for q in todo:
        for p in predecessors[q]:
            if p not in live:
                live.add(p); todo.append(p)
    old = sorted(live); remap = {q: i for i, q in enumerate(old)}
    return ([tuple(remap.get(q, -1) for q in rows[p]) for p in old],
            [pairs[p] for p in old], [heads[p] for p in old],
            {remap[p] for p in finals})


class _CapReached(Exception):
    pass


@dataclass
class _Work:
    max_nodes: Optional[int]
    max_chains: Optional[int]
    nodes: int = 0
    chains: int = 0

    def add_node(self):
        if self.max_nodes is not None and self.nodes >= self.max_nodes:
            raise _CapReached('Orbit-node cap')
        self.nodes += 1

    def add_chain(self):
        if self.max_chains is not None and self.chains >= self.max_chains:
            raise _CapReached('Orbit-chain cap')
        self.chains += 1


def _find_shared_uv(rows, finals, chain, work):
    work.add_chain()
    initial = (0, chain, False)
    work.add_node(); parent = {initial: None}; todo = deque([initial])
    while todo:
        node = todo.popleft(); phase, states, consumed = node
        if phase == 1 and consumed and states == chain[1:]:
            u, v = [], []; cur = node
            while parent[cur] is not None:
                prev, label = parent[cur]
                if label:
                    (u if prev[0] == 0 else v).append(label)
                cur = prev
            return ''.join(reversed(u)), ''.join(reversed(v))
        edges = []
        if phase == 0 and states[-1] in finals:
            edges.append(((1, states[:-1], False), ''))
        for a in (0, 1):
            nxt = tuple(rows[q][a] for q in states)
            if all(q >= 0 for q in nxt):
                edges.append(((phase, nxt, phase == 1), str(a)))
        for nxt, label in edges:
            if nxt not in parent:
                work.add_node(); parent[nxt] = (node, label); todo.append(nxt)
    return None


def check_regular_family_orbits(I: Instance, D: Instance,
                               max_nodes: Optional[int] = 100_000,
                               max_chains: Optional[int] = 10_000) -> dict:
    validate_binary(I); validate_binary(D)
    if D.flags or D.bad:
        raise ValueError('Domain must be an unannotated binary DFA')
    if any(x is not None and (type(x) is not int or x < 1)
           for x in (max_nodes, max_chains)):
        raise ValueError('Caps must be positive integers or None')
    boundary, member = _boundary_check(I, D)
    if boundary is not None:
        return boundary
    rows, pairs, heads, finals = _live_product(I, D)
    K = len(rows)
    terminal = all(all(q < 0 for q in I.delta[f]) for f in I.final)
    exponent_bound = min(K, len(I.delta)-1) if terminal else K
    work = _Work(max_nodes, max_chains)
    reach = []
    for p in range(K):
        reached = {q for q in rows[p] if q >= 0}; todo = list(reached)
        for q in todo:
            for r in rows[q]:
                if r >= 0 and r not in reached:
                    reached.add(r); todo.append(r)
        reach.append(sorted(reached))
    flagged = [(p, q) for p in range(K) for q in reach[p]
               if (pairs[p][0], pairs[q][0]) in I.flags]

    def chains(p, q, e):
        stack = [(p, q)]
        while stack:
            chain = stack.pop()
            if len(chain) == e+1:
                yield chain
                continue
            used = {pairs[j][0] for j in chain} if terminal else set()
            for r in reversed(reach[chain[-1]]):
                if not terminal or pairs[r][0] not in used:
                    stack.append(chain+(r,))
    try:
        for e in range(1, exponent_bound + 1):
            for p, q in flagged:
                for chain in chains(p, q, e):
                    if terminal and len({pairs[j][0] for j in chain}) != len(chain):
                        continue
                    result = _find_shared_uv(rows, finals, chain, work)
                    if result is not None:
                        u, v = result
                        word = heads[p] + (u+v)*e + u
                        return _bad_member(
                            I, D, word,
                            factorization=dict(head=heads[p], u=u, v=v, exponent=e),
                            flag=[pairs[p][0], pairs[q][0]],
                            product_states=K, nodes=work.nodes, chains=work.chains,
                            reason='Shared-word orbit product reached acceptance')
    except _CapReached as error:
        return dict(status='UNKNOWN', reason=str(error), product_states=K,
                    exponent_bound=exponent_bound, nodes=work.nodes, chains=work.chains)
    if not witness(I, member) or not border_witness(I, member):
        raise AssertionError('Claimed valid family has an invalid sample member')
    E = exponent_bound
    bound = K-1 + (E+1)*(K**(E+1)-1) + E*K**E
    return dict(status='REGULAR_FAMILY_VALID', inhabited=True, word=member,
                product_states=K, exponent_bound=E, nodes=work.nodes, chains=work.chains,
                proper_counterexample_length_bound=bound,
                reason='Complete shared-word orbit products exhausted',
                scope='Every domain word is a witness; NOT existential BorderAvoid')


def intersection_instance(automata):
    automata = tuple(automata)
    if not automata:
        raise ValueError('At least one automaton is required')
    for A in automata:
        validate_binary(A)
        if A.flags or A.bad:
            raise ValueError('Intersection inputs must be unannotated')
    if len(automata) == 1:
        automata = automata * 2
    entries, offsets, N = [], [], 0
    for A in automata:
        entries.append(N); offsets.append(N+1); N += len(A.delta)+1
    terminal = N; N += 1
    macro = [[-1, -1, -1] for _ in range(N)]
    for i, A in enumerate(automata):
        macro[entries[i]][1] = offsets[i] + A.start
        following = entries[i+1] if i+1 < len(automata) else terminal
        for p, row in enumerate(A.delta):
            macro[offsets[i]+p] = [offsets[i]+q if q >= 0 else -1 for q in row]
            macro[offsets[i]+p].append(following if p in A.final else -1)
    delta = [[-1, -1] for _ in range(3*N)]
    for p, (zero, one, marker) in enumerate(macro):
        if marker >= 0:
            delta[3*p][0] = 3*p+1; delta[3*p+1][0] = 3*marker
        if zero >= 0 or one >= 0:
            delta[3*p][1] = 3*p+2
            delta[3*p+2] = [3*zero if zero >= 0 else -1, 3*one if one >= 0 else -1]
    I = Instance(tuple(map(tuple, delta)), frozenset({3*terminal}),
                 frozenset({(3*entries[0], 3*entries[1])}), start=3*entries[0])
    return I, replace(I, flags=frozenset())


def encode_blocks(blocks):
    code = {'0': '10', '1': '11', '#': '00'}
    return ''.join(code[a] for w in blocks for a in '1'+w+'#')
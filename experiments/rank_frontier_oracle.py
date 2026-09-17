"""Independent all-length oracle for one FIXED rank reference and a query.

Unlike rank_preimage.py this retains the entire fixed old graph. It generates
one fresh strip online and forgets an interior vertex only after preserving
all observer-product reachability through it. This is not symbolic preimage
closure and not an unrestricted subtype decider. Python 3.10+, standard library.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import product

from rank_query_graphs import Colour, Graph, literal_graph
from rank_query_prefix import Reference


class OracleLimit(RuntimeError):
    pass


def close_relation(rows):
    """Warshall closure on bit-set rows; no call to the candidate path solver."""
    rows = list(rows)
    for pivot in range(len(rows)):
        bit, reachable = 1 << pivot, rows[pivot]
        for source in range(len(rows)):
            if rows[source] & bit:
                rows[source] |= reachable
    return tuple(rows)


def add_edges(observer, colours, edges, previous=(), max_nodes=4096):
    size, n = observer.size, len(colours) * observer.size
    if max_nodes is not None and n > max_nodes:
        raise OracleLimit('Explicit observer-product cap')
    rows = list(previous) + [0] * (n-len(previous))
    allowed = [observer.allows(q, c) for c in colours for q in range(size)]
    for i, good in enumerate(allowed):
        if good: rows[i] |= 1 << i
    for u, letter, v in edges:
        for q in range(size):
            if not allowed[u*size+q]: continue
            for p in observer.move(q, letter, colours[u], colours[v]):
                if allowed[v*size+p]: rows[u*size+q] |= 1 << (v*size+p)
    return close_relation(rows)


def restrict_relation(rows, keep, size):
    indices = [v*size+q for v in keep for q in range(size)]
    return tuple(sum(1 << j for j, old in enumerate(indices) if rows[i] >> old & 1)
                 for i in indices)


def check_bindings(query, colours, assignment, complete=False):
    d = dict(zip(query.variables, assignment))
    if complete and -1 in assignment: return False
    for v, test in query.tests:
        if d[v] >= 0 and not test.holds(colours[d[v]]): return False
    for pairs, equal in ((query.equal, True), (query.unequal, False)):
        for u, v in pairs:
            if d[u] >= 0 and d[v] >= 0 and ((d[u] == d[v]) != equal): return False
    return True


def assign_here(query, colours, assignment, vertex):
    unset = [i for i, v in enumerate(assignment) if v < 0]
    for bits in product((False, True), repeat=len(unset)):
        a = list(assignment)
        for i, choose in zip(unset, bits):
            if choose: a[i] = vertex
        a = tuple(a)
        if check_bindings(query, colours, a): yield a


def accepts_summary(query, colours, assignment, relations):
    if not check_bindings(query, colours, assignment, complete=True): return False
    d = dict(zip(query.variables, assignment))
    for atom, rows in zip(query.atoms, relations):
        o = atom.observer
        if not any(rows[d[atom.source]*o.size+q] >> (d[atom.target]*o.size+p) & 1
                   for q in o.initial for p in o.final): return False
    return True


def explicit_query_truth(graph, query, *, max_product_nodes=None):
    """Separate full-graph semantics: matrix closure plus exhaustive assignment."""
    relations = tuple(add_edges(a.observer, graph.colours, graph.edges, max_nodes=max_product_nodes)
                      for a in query.atoms)
    domains = []
    for v in query.variables:
        tests = [t for w, t in query.tests if v == w]
        domains.append([i for i, c in enumerate(graph.colours) if all(t.holds(c) for t in tests)])
    for assignment in product(*domains):
        if accepts_summary(query, graph.colours, assignment, relations): return True
    return False


@dataclass(frozen=True)
class Frontier:
    first_bit: str
    origin: int
    colours: tuple
    assignment: tuple[int, ...]
    relations: tuple


def fixed_reference_query(I, B, query, *, max_states=50000, max_product_nodes=4096,
                          require_terminal=True):
    """Decide if SOME safe first return of supplied B satisfies query.

    With no caps this exhausts a finite graph; a cap is UNKNOWN, not NO.
    require_terminal=False permits isolated graph-mechanism tests, not a change
    in the terminal theorem's semantic hypotheses.
    """
    if not B.word or len(B.labels) != len(B.word)+1:
        raise ValueError('Nonempty reference and all original cut labels required')
    k = len(I.delta)
    if any(type(q) is not int or not 0 <= q < k for q in B.labels):
        raise ValueError('Invalid original label')
    if any(a not in '01' for a in B.word): raise ValueError('Binary reference required')
    if require_terminal and (B.labels[0] not in I.final or
                             any(t >= 0 for f in I.final for t in I.delta[f])):
        raise ValueError('Terminal initial reverse label required')
    if any(I.delta[B.labels[i+1]][int(a)] != B.labels[i] for i, a in enumerate(B.word)):
        raise ValueError('Inconsistent reverse labels')
    G = literal_graph(I, B)
    if any(c.state in I.bad or c.forbidden >> c.state & 1 for c in G.colours):
        raise ValueError('Unsafe base reference')
    m, first = len(B.word), len(B.word)+1
    edge = {(u, a): v for u, a, v in G.edges}
    incoming = {(q, a): tuple(p for p, row in enumerate(I.delta) if row[a] == q)
                for q in range(k) for a in range(2)}
    masks = tuple(sum(1 << p for p in range(k) if (p, q) in I.flags) for q in range(k))
    def next_colours(q, h):
        if q in I.bad or (q, q) in I.flags or G.colours[h].forbidden >> q & 1: return
        for nb in (('',) if h == m else ('0', '1')):
            yield Colour(q, masks[q] | G.colours[h].forbidden, nb, False, h == m)
    def exits(v, h, colour, bit):
        out = [(v, 'F', h)]
        if colour.end:
            out.append((v, 'K'+bit, first))
            other = str(1-int(bit))
            out.append((v, 'K'+other, edge[m, 'K'+other]))
        else:
            other = str(1-int(colour.next_bit))
            out.append((v, 'K'+other, edge[h, 'K'+other]))
        return tuple(out)
    parent, queue = {}, deque()
    peak = 0
    def insert(state, prior, letter, q):
        nonlocal peak
        if state in parent: return
        if max_states is not None and len(parent) >= max_states:
            raise OracleLimit('Explicit frontier-state cap')
        parent[state] = (prior, letter, q)
        queue.append(state)
        peak = max(peak, len(state.colours))
    try:
        for bit in '01':
            h = edge[edge[m, 'F'], 'K'+bit]
            base = list(G.colours)
            c = base[m]
            base[m] = Colour(c.state, c.forbidden, bit, c.root, False)
            core_edges = [(u, a, v) for u, a, v in G.edges if not (u == m and a == 'K'+bit)]
            for q in incoming[B.labels[-1], int(bit)]:
                for c in next_colours(q, h):
                    colours = tuple(base)+(c,)
                    es = tuple(core_edges)+((m, 'S', first), (m, 'K'+bit, first))+exits(first, h, c, bit)
                    relations = tuple(add_edges(a.observer, colours, es, max_nodes=max_product_nodes)
                                      for a in query.atoms)
                    for old in product(range(-1, m+1), repeat=len(query.variables)):
                        if not check_bindings(query, colours, old): continue
                        for assigned in assign_here(query, colours, old, first):
                            insert(Frontier(bit, h, colours, assigned, relations), None, bit, q)
        while queue:
            node = queue.popleft()
            current = len(node.colours)-1
            colour = node.colours[current]
            if colour.end:
                if accepts_summary(query, node.colours, node.assignment, node.relations):
                    letters, labels, cursor = [], [], node
                    while cursor is not None:
                        cursor, letter, q = parent[cursor]
                        letters.append(letter); labels.append(q)
                    C = Reference(B.word+''.join(reversed(letters)), B.labels+tuple(reversed(labels)))
                    # Check the return condition by literal substring search.
                    assert C.word.find(B.word, 1)+m == len(C.word)
                    assert explicit_query_truth(literal_graph(I, C), query)
                    return dict(status='YES', reference=C.word, labels=list(C.labels),
                                states=len(parent), frontier_vertices=peak)
                continue
            bit = colour.next_bit
            h = edge[node.origin, 'K'+bit]
            for q in incoming[colour.state, int(bit)]:
                for new_colour in next_colours(q, h):
                    new_vertex = len(node.colours)
                    colours = node.colours+(new_colour,)
                    es = ((current, 'S', new_vertex), (current, 'K'+bit, new_vertex))
                    es += exits(new_vertex, h, new_colour, node.first_bit)
                    relations = tuple(add_edges(a.observer, colours, es, rows, max_product_nodes)
                                      for a, rows in zip(query.atoms, node.relations))
                    for assigned in assign_here(query, colours, node.assignment, new_vertex):
                        # No future edge can address this unmarked interior node.
                        keep = [i for i in range(len(colours))
                                if i != current or current == first or current in assigned]
                        remap = {old: new for new, old in enumerate(keep)}
                        bound = tuple(remap[v] if v >= 0 else -1 for v in assigned)
                        rs = tuple(restrict_relation(rows, keep, a.observer.size)
                                   for a, rows in zip(query.atoms, relations))
                        colours_kept = tuple(colours[i] for i in keep)
                        insert(Frontier(node.first_bit, h, colours_kept, bound, rs), node, bit, q)
        return dict(status='NO', states=len(parent), frontier_vertices=peak,
                    reason='Complete finite fixed-reference frontier exhausted')
    except (OracleLimit, MemoryError, RecursionError, OverflowError) as exc:
        return dict(status='UNKNOWN', states=len(parent), frontier_vertices=peak,
                    reason=str(exc))

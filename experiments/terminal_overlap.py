"""Exact terminal witness decisions when the last-flag overlap graph is acyclic.

A certificate is computed on a finite graph of ordered state pairs. Flagged
vertices may be visited only at the beginning: any later flag would provide
a shorter violating suffix. Cycles in the remaining graph obstruct THIS
certificate, not proof of nonexistence
or undecidability. An exhausted necessary-word graph is a genuine NO. All
positive words are independently checked. Binary Instance conventions apply.
"""
from collections import deque
from dataclasses import replace
from border_lab import Instance, Sandwich, witness, border_witness
from terminal_realization import validate


def _reach(starts, edges):
    seen = set(starts)
    todo = list(seen)
    for p in todo:
        for q in edges.get(p, ()):
            if q not in seen:
                seen.add(q)
                todo.append(q)
    return seen


def boundary_slice(instance, final):
    """Preserve exactly the witnesses ending at one terminal final state."""
    validate(instance)
    if final not in instance.final:
        raise ValueError('The slice endpoint must be an accepting state')
    if any(any(r >= 0 for r in instance.delta[f]) for f in instance.final):
        raise ValueError('All accepting states must be terminal')
    unsafe = set(instance.bad)
    unsafe.update(p for p, q in instance.flags if p == q or q == final)
    safe = set(range(len(instance.delta))) - unsafe
    graph = {p: [q for q in instance.delta[p] if q in safe] for p in safe}
    reverse = {p: [] for p in safe}
    for p, targets in graph.items():
        for q in targets:
            reverse[q].append(p)
    live = (_reach([instance.start], graph) & _reach([final], reverse) & safe)
    if instance.start not in live or final not in live:
        live = set()
    delta = tuple(tuple(q if p in live and q in live else -1 for q in row)
                  for p, row in enumerate(instance.delta))
    sliced = replace(instance, delta=delta, final=frozenset({final}),
                     bad=frozenset(set(range(len(delta))) - live))
    return sliced, live


def overlap_certificate(instance, final, max_pair_vertices=1000000):
    """Bound the shortest violating suffix length in any non-witness, not L+D.

    The bound need NOT bound all flagged agreements in the word. A later
    aligned flagged pair already witnesses a shorter violation. Thus roots
    can be flagged, but every positive successor must be unflagged.

    EMPTY_SLICE: there is no boundary-safe accepted word for this final.
    BOUNDED: Necessary(bound,0) equals Witness on the returned slice.
    CYCLIC: this sufficient certificate is unavailable. NOT a negative answer.
    UNKNOWN: an explicit construction cap was reached.
    """
    sliced, live = boundary_slice(instance, final)
    if not live:
        return dict(status='EMPTY_SLICE', final=final, bound=0, live_states=0), sliced
    internal = live - {final}
    graph = {p: [q for q in sliced.delta[p] if q in live] for p in live}
    reach = {p: _reach([p], graph) for p in internal}
    starts = {(p, q) for p, q in sliced.flags
              if p in internal and q in internal and p != q and q in reach[p]}
    if not starts:
        return dict(status='BOUNDED', final=final, bound=0,
                    live_states=len(live), pair_vertices=0, pair_edges=0,
                    start_pairs=[], longest_pair_path=[]), sliced
    if (len(live)-1)**2 > max_pair_vertices:
        return dict(status='UNKNOWN', reason='Pair construction cap', final=final), sliced
    # A last-flag path starts in G and never enters G again.
    unflagged = {(p, q) for p in internal for q in live
                 if p != q and (p, q) not in sliced.flags}
    vertices = unflagged | starts
    edges = {pair: [] for pair in vertices}
    reverse = {pair: [] for pair in vertices}
    for p, q in vertices:
        for a, (r, s) in enumerate(zip(sliced.delta[p], sliced.delta[q])):
            target = (r, s)
            if target in unflagged:
                edges[(p, q)].append(target)
                reverse[target].append((p, q))
    endpoints = {(p, final) for p in internal}
    relevant = _reach(starts, edges) & _reach(endpoints, reverse)
    edges = {p: [q for q in edges[p] if q in relevant] for p in relevant}
    indegree = {p: 0 for p in relevant}
    for targets in edges.values():
        for q in targets:
            indegree[q] += 1
    queue = deque(sorted(p for p in relevant if indegree[p] == 0))
    order = []
    while queue:
        p = queue.popleft()
        order.append(p)
        for q in edges[p]:
            indegree[q] -= 1
            if indegree[q] == 0:
                queue.append(q)
    info = dict(final=final, kind='last-flag detection bound',
                live_states=len(live), pair_vertices=len(relevant),
                pair_edges=sum(map(len, edges.values())),
                start_pairs=sorted(starts & relevant))
    if len(order) != len(relevant):
        return dict(info, status='CYCLIC',
                    reason='Relevant flag-free synchronized-pair graph contains a cycle',
                    residual_vertices=sorted(p for p in relevant if indegree[p] > 0)), sliced
    distance = {p: 0 for p in starts & relevant}
    parent = {p: None for p in distance}
    for p in order:
        if p not in distance:
            continue
        for q in edges[p]:
            if distance[p]+1 > distance.get(q, -1):
                distance[q] = distance[p]+1
                parent[q] = p
    end = max(endpoints & distance.keys(), key=lambda p: (distance[p], p), default=None)
    bound = distance[end] if end is not None else 0
    path = []
    while end is not None:
        path.append(end)
        end = parent[end]
    # At most (r-1)(r-2) internal pair vertices precede a terminal endpoint.
    assert bound <= max(0, (len(live)-1)*(len(live)-2))
    return dict(info, status='BOUNDED', bound=bound,
                longest_pair_path=list(reversed(path))), sliced


def bounded_overlap_decision(instance, max_states=200000, max_pair_vertices=1000000):
    """Exact on certified slices; retain UNKNOWN for cyclic/capped remainders."""
    validate(instance)
    if any(any(r >= 0 for r in instance.delta[f]) for f in instance.final):
        return dict(status='UNKNOWN', reason='Nonterminal accepting state')
    diagnostics = []
    unresolved = False
    for final in sorted(instance.final):
        certificate, sliced = overlap_certificate(instance, final, max_pair_vertices)
        row = dict(certificate=certificate)
        diagnostics.append(row)
        status = certificate['status']
        if status == 'EMPTY_SLICE':
            continue
        if status != 'BOUNDED':
            unresolved = True
            continue
        answer = Sandwich(sliced, certificate['bound'], 0).search(max_states)
        row['search'] = answer
        if answer['status'] == 'YES':
            w = answer['word']
            if not witness(instance, w) or not border_witness(instance, w):
                raise AssertionError('Certificate disagrees with an independent word predicate')
            return dict(status='YES', word=w, slices=diagnostics)
        if answer['status'] != 'NO':
            unresolved = True
    if unresolved:
        return dict(status='UNKNOWN', reason='At least one final slice is uncertified or capped',
                    slices=diagnostics)
    return dict(status='NO', reason='Every final slice is exactly empty', slices=diagnostics)

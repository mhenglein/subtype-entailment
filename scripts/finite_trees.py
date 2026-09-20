"""Independent finite-tree growth diagnostics and graph finiteness checks.

The CLI decision uses Lean FiniteTreeDecision. This ordinary implementation
is retained as an independent diagnostic and reference for native comparisons. Epsilon cycles alone do not imply infinite growth.
"""
from collections import deque

import regular_countermodel as regular


def growth_analysis(system, deadline=None):
    """Classify reverse-pop infiniteness and return a nonempty loop witness.

    T is reachability using balanced epsilon edges and reverse-pop letter edges.
    A letter edge p-a->r lies on a consuming cycle iff r reaches p. Initial
    controls are unrestricted, so every endpoint reachable after such a cycle
    has an infinite reverse-pop language from some initial control.
    """
    reverse = system.reverse()
    epsilon = regular.balanced(reverse, deadline)
    rows = epsilon[:]
    for p, a, q in reverse.pop:
        rows[p] |= 1 << q
    regular.transitive_closure(rows, deadline)
    hot = 0
    cycle_edge = None
    for p, a, r in sorted(reverse.pop):
        regular.check_time(deadline)
        if rows[r] & (1 << p):
            hot |= rows[r]
            if cycle_edge is None:
                cycle_edge = p, a, r
    result = {'hot': list(regular.bits(hot)), 'controls': system.size,
              'cycle': None, 'has_consuming_cycle': bool(hot)}
    if cycle_edge is None:
        return result
    p, a, r = cycle_edge
    # Recover a finite path r -> p, retaining only its letter labels. A balanced
    # epsilon edge consumes nothing even if its underlying stack excursion grows.
    queue, paths = deque([r]), {r: ()}
    pops = [[] for _ in range(system.size)]
    for x, b, y in sorted(reverse.pop):
        pops[x].append((y, b))
    while p not in paths:
        regular.check_time(deadline)
        x = queue.popleft()
        for y, b in [(y, None) for y in regular.bits(epsilon[x])] + pops[x]:
            if y not in paths:
                paths[y] = paths[x] + (() if b is None else (b,))
                queue.append(y)
    word = (a,) + paths[p]
    if not (regular.PopMachine(reverse, deadline).run(p, word) & (1 << p)):
        raise ValueError('recovered word is not a reverse-pop loop')
    result['cycle'] = {'control': p, 'word': list(word), 'forced_root': p in system.forced}
    return result


def finite_graph_height(nodes, roots, deadline=None):
    """Return a finite height, or None for a cycle reachable from the roots.

    Bottom has height zero, products one plus the maximum child height.
    Unreachable nodes have no effect on the valuation's finiteness.
    """
    roots = tuple(roots)
    done, active = {}, set()
    for root in roots:
        pending = [(root, False)]
        while pending:
            regular.check_time(deadline)
            q, finish = pending.pop()
            if q in done:
                continue
            if nodes[q] is None:
                done[q] = 0
                continue
            if finish:
                active.remove(q)
                done[q] = 1 + max(done[child] for child in nodes[q])
                continue
            if q in active:
                return None
            active.add(q)
            pending.append((q, True))
            pending.extend((child, False) for child in nodes[q])
    return max((done[r] for r in roots), default=0)


def analyze_problem(problem, deadline=None):
    system = regular.normalize(problem, deadline)
    result = growth_analysis(system, deadline)
    if result['cycle'] is not None and not result['cycle']['forced_root']:
        raise ValueError('normalization produced a reverse-pop cycle without its required forced root')
    result['finite_model_obstruction'] = result['has_consuming_cycle']
    result['basis'] = 'independent Python growth diagnostic; CLI decision uses Lean FiniteTreeDecision'
    return result


def check_countermodel(problem, model, deadline=None):
    """Validate original expressions, then rule out cycles at variable roots."""
    from subtail import check_countermodel as check_regular
    checked = check_regular(problem, model, deadline)
    if not checked['valid']:
        return checked
    height = finite_graph_height(checked['nodes'], checked['roots'].values(), deadline)
    if height is None:
        return {'valid': False, 'reason': 'infinite_variable_tree'}
    return {**checked, 'finite_height': height,
            'semantics': 'finite bottom/product trees; all variable roots unfold to finite trees'}

"""Finite-tree reduction for the exact bottom/product signature.

Ordinary implementation, with its proof and formal boundaries in the dated
finite-tree reduction note. Epsilon cycles alone do not imply infinite growth.
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
    result['basis'] = 'ordinary finite-tree reduction; growth classifier is not Lean-verified'
    return result


def run_analysis(problem, deadline, memory_gib=16.0):
    """Run normalization/classification with the CLI's process resource limits."""
    import json
    from pathlib import Path
    import sys
    import tempfile
    import time
    from subtail import ROOT, problem_json, run_process
    with tempfile.TemporaryDirectory(prefix='subtail-finite-') as directory:
        source, target = Path(directory) / 'input.json', Path(directory) / 'growth.json'
        source.write_text(json.dumps(problem_json(problem)))
        remaining = deadline - time.monotonic()
        run = run_process([sys.executable, str(ROOT / 'scripts/finite_trees.py'),
                           str(source), str(target), str(max(0, remaining))],
                          ROOT, remaining, memory_gib)
        if run['status'] != 'PASS':
            return {k: v for k, v in run.items() if k != 'output'}
        if not target.exists() or target.stat().st_size > 8 * 1024**2:
            return {'status': 'UNKNOWN', 'reason': 'missing_or_oversize_growth_result'}
        try:
            result = json.loads(target.read_text())
            if type(result.get('finite_model_obstruction')) is not bool:
                raise ValueError('missing growth Boolean')
            return {**result, 'status': 'PASS'}
        except (ValueError, AttributeError):
            return {'status': 'UNKNOWN', 'reason': 'invalid_growth_result'}


def run_decision(problem, deadline, memory_gib=16.0):
    from subtail import run_native
    growth = run_analysis(problem, deadline, memory_gib)
    if growth['status'] != 'PASS':
        return {**growth, 'stage': 'finite_growth_analysis'}
    if growth['finite_model_obstruction']:
        return {'status': 'ENTAILED', 'stage': 'finite_growth_analysis',
                'reason': 'no_finite_model', 'growth_analysis': growth,
                'basis': 'ordinary finite-tree cycle reduction; vacuous entailment'}
    result = run_native(problem, deadline, memory_gib)
    return {**result, 'growth_analysis': growth,
            'arbitrary_tree_basis': result.get('basis'),
            'basis': 'ordinary finite-tree cycle reduction followed by Lean arbitrary-tree decision'}


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


if __name__ == '__main__':
    import json
    from pathlib import Path
    import sys
    import time
    from subtail import parse_problem
    problem = parse_problem(json.loads(Path(sys.argv[1]).read_text()))
    result = analyze_problem(problem, time.monotonic() + float(sys.argv[3]))
    Path(sys.argv[2]).write_text(json.dumps(result))

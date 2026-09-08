"""Exact target-frontier certificates with arbitrarily many early markers.

All suffix comparisons are retained. Marker cycles before the first relevant
flag target are allowed; marker cycles reachable from such a target are not.
This is a certified subclass, NOT an unrestricted BorderAvoid decision.
The new all-length arguments are written proofs, pending independent review.
"""
from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Dict, FrozenSet, Optional, Tuple

from border_lab import witness, border_witness
from terminal_realization import validate
from marker_certificate import boundary_slice, reach


@dataclass(frozen=True)
class Limits:
    states: Optional[int] = 100000
    transitions: Optional[int] = 1000000
    descriptors: Optional[int] = 100000
    schemas: Optional[int] = 2000
    reconstruction: Optional[int] = 200000

    def __post_init__(self):
        for value in self.__dict__.values():
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError('Caps must be positive integers or None')


@dataclass
class Macro:
    delta: Dict[int, Tuple[int, int, int]]  # data 0, data 1, marker
    start: int
    final: int
    flags: FrozenSet[Tuple[int, int]]
    code: str = 'paired'

    @property
    def targets(self):
        return frozenset(q for p, q in self.flags)

    def expand(self, blocks):
        if self.code == 'unary':
            if any('0' in u for u in blocks):
                raise ValueError('Unary macro data may contain only 1')
            return ''.join(u + '0' for u in blocks)
        return ''.join(''.join('1' + a for a in u) + '00' for u in blocks)


def parse_macro(instance, final, code='paired'):
    """Validate the old token format, without forbidding early marker cycles."""
    sliced, live = boundary_slice(instance, final)
    if sliced is None:
        return dict(status='EMPTY_SLICE', final=final), None
    if sliced.start == final:
        return dict(status='EMPTY_WORD', final=final), None
    if code not in ('paired', 'unary'):
        raise ValueError('Unknown code')
    parser = (((2, 1), (0, 0), (3, 4), (2, 1), (4, 4)) if code == 'paired'
              else ((3, 0),) * 5)
    seen = {(sliced.start, 0)}
    todo = list(seen)
    for q, phase in todo:
        if q == final and phase != 3:
            return dict(status='NOT_APPLICABLE', reason='Accepted word outside token format'), None
        for a, t in enumerate(sliced.delta[q]):
            if t >= 0:
                nxt = (t, parser[phase][a])
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
    relevant = frozenset((p, q) for p, q in sliced.flags
                         if p in live and q in live and p != final)
    odd = {q for q, phase in seen if phase in (1, 2)} if code == 'paired' else set()
    if any(p in odd or q in odd for p, q in relevant):
        return dict(status='NOT_APPLICABLE', reason='Flag endpoint inside a token'), None
    boundary = {q for q, phase in seen if phase in (0, 3)}
    table = {}
    for q in boundary:
        row = []
        for token in (('10', '11', '00') if code == 'paired' else (None, '1', '0')):
            t = q
            if token is None:
                row.append(-1)
                continue
            for a in token:
                t = sliced.delta[t][int(a)]
                if t < 0:
                    break
            row.append(t if t in boundary else -1)
        table[q] = tuple(row)
    graph = {p: [q for q in row if q >= 0] for p, row in table.items()}
    reverse = {q: [] for q in table}
    for p, qs in graph.items():
        for q in qs:
            reverse[q].append(p)
    useful = reach([sliced.start], graph) & reach([final], reverse)
    table = {p: tuple(q if q in useful else -1 for q in table[p]) for p in useful}
    flags = frozenset((p, q) for p, q in relevant if p in useful and q in useful)
    macro = Macro(table, sliced.start, final, flags, code)
    return dict(status='FORMATTED', final=final, code=code, macro_states=len(table)), macro


def frontier_structure(macro):
    """Certify that no productive marker cycle is reachable from a target."""
    graph = {p: [q for q in row if q >= 0] for p, row in macro.delta.items()}
    cone = reach(macro.targets, graph)
    early_cycles = []
    for p, row in sorted(macro.delta.items()):
        q = row[2]
        if q >= 0 and p in reach([q], graph):
            if p in cone:
                return dict(status='NOT_APPLICABLE', reason='Marker cycle reachable from a flag target',
                            marker_edge=(p, q)), cone
            early_cycles.append((p, q))
    k = len(macro.delta)
    return dict(status='CERTIFIED', targets=sorted(macro.targets),
                target_cone_states=len(cone), early_cyclic_marker_edges=early_cycles,
                maximum_reference_blocks=max(0, k-1),
                prefix_blocks_bound_formula='K * 2**(r-1) - 1'), cone


def target_free_word(macro):
    """Every accepted path avoiding relevant targets is automatically a witness."""
    if macro.start in macro.targets:
        return None
    parent = {macro.start: None}
    todo = deque([macro.start])
    while todo:
        q = todo.popleft()
        if q == macro.final:
            labels = []
            while parent[q] is not None:
                q, label = parent[q]
                labels.append(label)
            logical = ''.join(reversed(labels))
            assert logical.endswith('#')
            return tuple(logical[:-1].split('#'))
        for a, t in zip('01#', macro.delta[q]):
            if t >= 0 and t not in macro.targets and t not in parent:
                parent[t] = (q, a)
                todo.append(t)
    return None


class SearchCap(RuntimeError):
    """Resource exhaustion must propagate as UNKNOWN."""


def reference_schemas(macro, prefix_cap=None):
    """Finite suffix schemas: the first block contains the first target.

    This enumerates reference suffixes, not the potentially unbounded early
    marker sequence. The first-block target visit is checked by the solver.
    """
    data = {p: [q for q in row[:2] if q >= 0] for p, row in macro.delta.items()}
    data_reach = {p: reach([p], data) for p in macro.delta}
    free = set(macro.delta) - set(macro.targets)
    free_graph = {p: [q for q in macro.delta[p] if q in free] for p in free}
    free_reached = reach([macro.start], free_graph) & free
    cuts = {macro.start}
    cuts.update(macro.delta[p][2] for p in free_reached if macro.delta[p][2] >= 0)
    prefixes = 0
    for cut in sorted(cuts):
        seen_target = set()
        for t in data_reach[cut] & macro.targets:
            seen_target.update(data_reach[t])
        for end in sorted(seen_target):
            after = macro.delta[end][2]
            if after < 0:
                continue
            first = ((cut, end, after),)
            pending = [(after, first)]
            while pending:
                at, schema = pending.pop()
                prefixes += 1
                if prefix_cap is not None and prefixes > prefix_cap:
                    raise SearchCap('Reference schema-prefix cap')
                assert len(schema) <= len(macro.delta)-1
                if at == macro.final:
                    yield schema
                    continue
                for b in sorted(data_reach[at], reverse=True):
                    t = macro.delta[b][2]
                    if t >= 0:
                        pending.append((t, schema + ((at, b, t),)))


def _pred(macro, allowed):
    result = {q: [] for q in allowed}
    for p in sorted(allowed):
        for a, q in enumerate(macro.delta[p][:2]):
            if q in allowed:
                result[q].append((str(a), p))
    return result


def _source_observe(q, eq, hits, done, refs, flags):
    if not done:
        for j, rj in enumerate(refs):
            if rj >= 0 and eq >> j & 1 and (q, rj) in flags:
                hits |= 1 << j
    return hits


def source_step(descriptors, columns, refs, pred, flags):
    """Subset update for ALL possible earlier blocks, relative to one suffix."""
    out = set()
    for end, q, eq, hits, done in descriptors:
        options = [('_', q, True)]
        if not done:
            options.extend((a, p, False) for a, p in pred[q])
        for a, p, finished in options:
            e = eq
            for j, b in enumerate(columns):
                if a != b:
                    e &= ~(1 << j)
            h = _source_observe(p, e, hits, finished, refs, flags)
            out.add((end, p, e, h, finished))
    return frozenset(out)


def complete_observations(macro, descriptors, pred):
    """Finish the unbounded source prefix after every reference word has ended."""
    reverse = {q: [p for _, p in xs] for q, xs in pred.items()}
    closure = {}
    result = set()
    for end, q, eq, hits, done in descriptors:
        starts = [q]
        if not done:
            assert eq == 0  # every reference already emitted padding
            if q not in closure:
                closure[q] = reach([q], reverse)
            starts = closure[q]
        for start in starts:
            result.add((start, macro.delta[end][2], eq, hits, end))
    return result


def pending_step(pending, equal, hits, r):
    """A finite forward monitor for comparisons sourced before the reference."""
    out = 0
    for j in range(1, r):
        if pending >> j & 1 and equal >> j & 1:
            if j == r-1:
                return None
            out |= 1 << (j+1)
    if hits >> (r-1) & 1:
        return None
    for j in range(r-1):
        if hits >> j & 1:
            out |= 1 << (j+1)
    return out


def prefix_path(macro, cut, observations, ref_equal, pair_bit, r, cap=None):
    def same(i, j):
        return i == j or bool(ref_equal & pair_bit[min(i,j), max(i,j)])
    # Existing pending checks can complete within the retained reference suffix.
    forbidden_pending = sum(1 << t for t in range(1, r)
                            if all(same(h, t+h) for h in range(r-t)))
    edges = {}
    for obs in sorted(observations):
        edges.setdefault(obs[0], []).append(obs)
    first = (macro.start, 0)
    parent = {first: None}
    todo = deque([first])
    while todo:
        q, mask = state = todo.popleft()
        if q == cut and not mask & forbidden_pending:
            path = []
            while parent[state] is not None:
                state, edge = parent[state]
                path.append(edge)
            path.reverse()
            assert len(path) <= len(macro.delta)*(1 << (r-1))-1
            return path
        for obs in edges.get(q, ()):
            _, target, eq, hits, _ = obs
            nxt_mask = pending_step(mask, eq, hits, r)
            nxt = (target, nxt_mask)
            if nxt_mask is not None and nxt not in parent:
                if cap is not None and len(parent) >= cap:
                    raise SearchCap('Prefix monitor cap')
                parent[nxt] = (state, obs)
                todo.append(nxt)
    return None


def recover_block(macro, schema, refs, desired, pred, cap):
    """Recover an earlier block from a certified observation; finite replay."""
    start, target, wanted_eq, wanted_hits, end = desired
    r = len(refs)
    traces = []
    for (begin, expected, _), word in zip(schema, refs):
        path = [begin]
        for a in word:
            path.append(macro.delta[path[-1]][int(a)])
        assert path[-1] == expected
        traces.append(path)
    maximum = max(map(len, refs), default=0)+1

    def coordinates(t):
        return tuple(tr[len(u)-t] if t <= len(u) else -1 for tr, u in zip(traces, refs))

    def column(t):
        return tuple(u[len(u)-t-1] if t < len(u) else '_' for u in refs)

    eq = (1 << r)-1
    h = _source_observe(end, eq, 0, False, coordinates(0), macro.flags)
    first = (0, end, eq, h, False)
    parent = {first: None}
    todo = deque([first])
    while todo:
        t, q, eq, hits, done = state = todo.popleft()
        if done and t == maximum and (q, eq, hits) == (start, wanted_eq, wanted_hits):
            rev = []
            while parent[state] is not None:
                state, a = parent[state]
                if a != '_':
                    rev.append(a)
            # Backtracking reverses the reverse-reading order already.
            return ''.join(rev)
        options = [('_', q, True)] if done or q == start else []
        if not done:
            options.extend((a, p, False) for a, p in pred[q])
        for a, p, finished in options:
            nt = min(t+1, maximum)
            e = eq
            for j, b in enumerate(column(t)):
                if a != b:
                    e &= ~(1 << j)
            h = _source_observe(p, e, hits, finished, coordinates(nt), macro.flags)
            nxt = (nt, p, e, h, finished)
            if nxt not in parent:
                if cap is not None and len(parent) >= cap:
                    return None
                parent[nxt] = (state, a)
                todo.append(nxt)
    raise AssertionError('An observation has no concrete source block')


def solve_schema(macro, schema, limits=Limits()):
    """Choose the reference words AND all possible prefix-block observations."""
    r = len(schema)
    pairs = tuple((i, j) for i in range(r) for j in range(i+1, r))
    bit = {pair: 1 << j for j, pair in enumerate(pairs)}
    all_ref_eq = (1 << len(pairs))-1
    all_src_eq = (1 << r)-1
    ref_pred = _pred(macro, set(macro.delta))
    free = set(macro.delta) - set(macro.targets)
    src_pred = _pred(macro, free)
    cut = schema[0][0]
    ends = [q for q in free if macro.delta[q][2] >= 0
            and (macro.delta[q][2] in free or macro.delta[q][2] == cut)]
    guard = {p: sum(bit[p[0]+h, p[1]+h] for h in range(1, r-p[1])) for p in pairs}

    def ref_observe(coords, eq, hits):
        for i, j in pairs:
            if coords[i] >= 0 and coords[j] >= 0 and eq & bit[i,j]:
                if (coords[i], coords[j]) in macro.flags:
                    hits |= bit[i,j]
        if any(hits & bit[p] and guard[p] == 0 for p in pairs):
            return None
        return hits

    coords = tuple(end for _, end, _ in schema)
    rh = ref_observe(coords, all_ref_eq, 0)
    if rh is None:
        return dict(status='NO', reason='Unavoidable empty-tail reference comparison', states=0, transitions=0)
    descriptors = frozenset((q, q, all_src_eq,
                            _source_observe(q, all_src_eq, 0, False, coords, macro.flags), False)
                           for q in ends)
    if limits.descriptors is not None and len(descriptors) > limits.descriptors:
        return dict(status='UNKNOWN', reason='Initial descriptor cap', states=0, transitions=0)
    first = (coords, all_ref_eq, rh, coords[0] in macro.targets, descriptors)
    parent = {first: None}
    todo = deque([first])
    steps = 0
    maximum_descriptors = len(descriptors)
    while todo:
        coords, eq, hits, seen_target, descriptors = state = todo.popleft()
        if all(q < 0 for q in coords):
            if not seen_target or any(hits & bit[p] and eq & guard[p] == guard[p] for p in pairs):
                continue
            observations = complete_observations(macro, descriptors, src_pred)
            try:
                path = prefix_path(macro, cut, observations, eq, bit, r, limits.states)
            except SearchCap as error:
                return dict(status='UNKNOWN', reason=str(error), states=len(parent), transitions=steps)
            if path is None:
                continue
            cols, cursor = [], state
            while parent[cursor] is not None:
                cursor, col = parent[cursor]
                cols.append(col)
            cols.reverse()
            refs = tuple(''.join(col[j] for col in cols if col[j] != '_')[::-1] for j in range(r))
            prefix = []
            for obs in path:
                u = recover_block(macro, schema, refs, obs, src_pred, limits.reconstruction)
                if u is None:
                    return dict(status='UNKNOWN', reason='Witness reconstruction cap', states=len(parent), transitions=steps)
                # Beyond every reference tail the equality bits are all false;
                # a shortest unmatched left extension is a simple data path.
                assert len(u) <= max(map(len, refs), default=0) + len(macro.delta)
                prefix.append(u)
            return dict(status='YES', word=macro.expand(tuple(prefix)+refs), prefix_blocks=prefix,
                        reference_blocks=refs, reference_schema=schema,
                        prefix_count_bound=len(macro.delta)*(1 << (r-1))-1,
                        states=len(parent), transitions=steps, max_descriptors=maximum_descriptors)
        options = []
        for j, q in enumerate(coords):
            if q < 0:
                options.append([('_', -1)])
            else:
                xs = list(ref_pred[q])
                if q == schema[j][0]:
                    xs.append(('_', -1))
                options.append(xs)
        for choices in product(*options):
            steps += 1
            if limits.transitions is not None and steps > limits.transitions:
                return dict(status='UNKNOWN', reason='Reference transition cap', states=len(parent), transitions=steps)
            column = tuple(a for a, _ in choices)
            nc = tuple(q for _, q in choices)
            ne = eq
            for i, j in pairs:
                if column[i] != column[j]:
                    ne &= ~bit[i,j]
            nh = ref_observe(nc, ne, hits)
            if nh is None:
                continue
            nd = source_step(descriptors, column, nc, src_pred, macro.flags)
            maximum_descriptors = max(maximum_descriptors, len(nd))
            if limits.descriptors is not None and len(nd) > limits.descriptors:
                return dict(status='UNKNOWN', reason='Source descriptor cap', states=len(parent), transitions=steps)
            ns = (nc, ne, nh, seen_target or nc[0] in macro.targets, nd)
            if ns not in parent:
                if limits.states is not None and len(parent) >= limits.states:
                    return dict(status='UNKNOWN', reason='Reference state cap', states=len(parent), transitions=steps)
                parent[ns] = (state, column)
                todo.append(ns)
    return dict(status='NO', reason='Entire finite reference/observation graph exhausted',
                states=len(parent), transitions=steps, max_descriptors=maximum_descriptors)


def target_frontier_decision(instance, limits=Limits()):
    validate(instance)
    if any(any(q >= 0 for q in instance.delta[f]) for f in instance.final):
        return dict(status='UNKNOWN', reason='Terminal accepting states required')
    rows = []
    unresolved = False
    total_schemas = 0
    for final in sorted(instance.final):
        chosen = None
        attempts = []
        for code in ('paired', 'unary'):
            fmt, macro = parse_macro(instance, final, code)
            if fmt['status'] == 'EMPTY_SLICE':
                chosen = ('EMPTY_SLICE', None, fmt)
                break
            if fmt['status'] == 'EMPTY_WORD':
                assert witness(instance, '') and border_witness(instance, '')
                return dict(status='YES', word='', slices=rows)
            if macro is None:
                attempts.append(dict(code=code, **fmt))
                continue
            free_word = target_free_word(macro)
            if free_word is not None:
                word = macro.expand(free_word)
                assert witness(instance, word) and border_witness(instance, word)
                return dict(status='YES', word=word, reason='Target-free accepting path', slices=rows)
            cert, cone = frontier_structure(macro)
            if cert['status'] == 'CERTIFIED':
                chosen = ('CERTIFIED', macro, dict(fmt, **cert))
                break
            attempts.append(dict(code=code, **cert))
        if chosen is None:
            unresolved = True
            rows.append(dict(final=final, attempts=attempts, status='UNKNOWN'))
            continue
        status, macro, cert = chosen
        row = dict(final=final, certificate=cert, schemas=[])
        rows.append(row)
        if status == 'EMPTY_SLICE':
            continue
        try:
            schemas = reference_schemas(macro, limits.schemas)
            for schema in schemas:
                if limits.schemas is not None and total_schemas >= limits.schemas:
                    return dict(status='UNKNOWN', reason='Reference schema cap', slices=rows, schemas=total_schemas)
                total_schemas += 1
                out = solve_schema(macro, schema, limits)
                row['schemas'].append(dict(schema=schema, result=out))
                if out['status'] == 'YES':
                    assert witness(instance, out['word']) and border_witness(instance, out['word'])
                    return dict(status='YES', word=out['word'], result=out, slices=rows, schemas=total_schemas)
                if out['status'] != 'NO':
                    unresolved = True
        except SearchCap as error:
            unresolved = True
            row['cover_cap'] = str(error)
    return dict(status='UNKNOWN' if unresolved else 'NO',
                reason='Uncertified or capped slice' if unresolved else 'All certified reference schemas are empty',
                slices=rows, schemas=total_schemas)

"""Recognize a bounded-marker class of raw binary terminal Instances.

No delimiter is inserted. The paired format uses 10/11 data and 00 markers;
the unary format uses data 1 and marker 0. Candidates must end in a marker.
In paired mode all relevant flags must be at token boundaries. No productive macro cycle may contain a separator. The
resulting finite family of schemas is complete for that certified slice.
Failure of a certificate or resource exhaustion is UNKNOWN, never NO.
"""
from collections import deque
from dataclasses import replace
from border_lab import Instance, witness, border_witness
from terminal_realization import validate
from word_sync import BinaryDFA
from delimited_blocks import BlockSystem, solve_blocks


def reach(starts, graph):
    seen = set(starts)
    todo = list(seen)
    for q in todo:
        for p in graph.get(q, ()):
            if p not in seen:
                seen.add(p)
                todo.append(p)
    return seen


def boundary_slice(I, f):
    unsafe = set(I.bad) | {p for p, q in I.flags if p == q or q == f}
    live = set(range(len(I.delta))) - unsafe
    graph = {p: [q for q in I.delta[p] if q in live] for p in live}
    rev = {p: [] for p in live}
    for p, qs in graph.items():
        for q in qs:
            rev[q].append(p)
    live &= reach([I.start], graph) & reach([f], rev)
    if I.start not in live or f not in live:
        return None, set()
    D = tuple(tuple(q if p in live and q in live else -1 for q in row)
              for p, row in enumerate(I.delta))
    J = replace(I, delta=D, final=frozenset({f}),
                bad=frozenset(set(range(len(D))) - live))
    return J, live


def marker_structure(I, f, code='paired'):
    """Return (certificate, sliced Instance, macro transitions).

    Parser states: 0=data boundary, 1=after 1, 2=after 0,
    3=after completed 00, 4=invalid. Only 3 accepts a complete candidate.
    """
    J, live = boundary_slice(I, f)
    if J is None:
        return dict(status='EMPTY_SLICE', final=f), None, None
    if I.start == f:
        return dict(status='EMPTY_WORD', final=f), J, None
    if code not in ('paired', 'unary'):
        raise ValueError('Unknown marker code')
    parser = (((2, 1), (0, 0), (3, 4), (2, 1), (4, 4))
              if code == 'paired' else ((3, 0), (3, 0), (3, 0), (3, 0), (3, 0)))
    seen = {(J.start, 0)}
    todo = list(seen)
    for q, phase in todo:
        if q == f and phase != 3:
            return dict(status='NOT_APPLICABLE', final=f,
                        reason='Some safe accepted word is outside the fixed token format'), J, None
        for a, t in enumerate(J.delta[q]):
            if t >= 0:
                nxt = (t, parser[phase][a])
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
    odd = {q for q, phase in seen if phase in (1, 2)} if code == 'paired' else set()
    flags = {(p, q) for p, q in J.flags if p in live and q in live and p != f}
    if any(p in odd or q in odd for p, q in flags):
        return dict(status='NOT_APPLICABLE', final=f,
                    reason='A relevant flag endpoint can occur inside a two-bit token'), J, None
    boundary = {q for q, phase in seen if phase in (0, 3)}
    macro = {}
    for q in boundary:
        row = []
        for token in (('10', '11', '00') if code == 'paired' else (None, '1', '0')):
            if token is None:
                row.append(-1)
                continue
            t = q
            for a in token:
                t = J.delta[t][int(a)]
                if t < 0:
                    break
            row.append(t if t in boundary else -1)
        macro[q] = tuple(row)
    graph = {p: [q for q in row if q >= 0] for p, row in macro.items()}
    rev = {q: [] for q in boundary}
    for p, qs in graph.items():
        for q in qs:
            rev[q].append(p)
    productive = reach([J.start], graph) & reach([f], rev) & boundary
    macro = {p: tuple(q if q in productive else -1 for q in macro[p]) for p in productive}
    graph = {p: [q for q in row if q >= 0] for p, row in macro.items()}
    for p, row in macro.items():
        q = row[2]
        if q >= 0 and p in reach([q], graph):
            return dict(status='NOT_APPLICABLE', final=f,
                        reason='A productive cycle contains a separator',
                        separator_edge=(p, q)), J, None
    return dict(status='CERTIFIED', final=f, code=code, macro_states=len(productive),
                maximum_blocks=max(0, len(productive)-1),
                parser_product_states=len(seen)), J, macro


def marker_decision(I, max_schemas=5000, max_states=200000, max_transitions=2000000):
    """Sound raw-Instance front end, exact on the certified bounded-marker class.

    UNKNOWN may coexist with certified slices; any genuine positive slice still
    returns YES. No claimed completeness outside the explicit certificate.
    """
    validate(I)
    if I.alphabet != '01' or any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        return dict(status='UNKNOWN', reason='Binary terminal accepting states are required')
    if max_schemas is not None and (type(max_schemas) is not int or max_schemas < 1):
        raise ValueError('max_schemas must be a positive integer or None')
    rows = []
    unresolved = False
    total_schemas = 0
    for f in sorted(I.final):
        cert, J, macro = marker_structure(I, f)
        if cert['status'] == 'NOT_APPLICABLE':
            paired_failure = cert['reason']
            cert, J, macro = marker_structure(I, f, code='unary')
            cert['paired_failure'] = paired_failure
        row = dict(certificate=cert, schemas=0)
        rows.append(row)
        if cert['status'] == 'EMPTY_SLICE':
            continue
        if cert['status'] == 'EMPTY_WORD':
            assert witness(I, '') and border_witness(I, '')
            return dict(status='YES', word='', slices=rows, schemas=total_schemas)
        if cert['status'] != 'CERTIFIED':
            unresolved = True
            continue
        k = len(I.delta)
        data = {p: [q for q in a[:2] if q >= 0] for p, a in macro.items()}
        data_reach = {p: reach([p], data) for p in macro}
        # Stack enumerates separator edge sequences. No separator can be on a
        # macro cycle, so every extension strictly advances in the SCC DAG.
        todo = [(J.start, ())]
        while todo:
            start, edges = todo.pop()
            for end in sorted(data_reach[start], reverse=True):
                target = macro[end][2]
                if target < 0:
                    continue
                seq = edges + ((start, end, target),)
                assert len(seq) <= cert['maximum_blocks']
                if target != f:
                    todo.append((target, seq))
                    # Cap queued schema prefixes too; otherwise enumerating an
                    # incomplete cover could consume unbounded practical memory.
                    if max_schemas is not None and len(todo) > max_schemas:
                        return dict(status='UNKNOWN', reason='Schema-prefix cap', slices=rows,
                                    schemas=total_schemas)
                    continue
                if max_schemas is not None and total_schemas >= max_schemas:
                    return dict(status='UNKNOWN', reason='Schema cap', slices=rows,
                                schemas=total_schemas)
                total_schemas += 1
                row['schemas'] += 1
                r = len(seq)
                table = tuple(macro[p][:2] if p in macro else (-1, -1) for p in range(k))
                ms = tuple(BinaryDFA(table, frozenset({end}), begin) for begin, end, _ in seq)
                flags = frozenset(((i, p), (j, q)) for i in range(r) for j in range(r)
                                  for p, q in J.flags if p in macro and q in macro)
                system = BlockSystem(ms, flags)
                answer = solve_blocks(system, max_states=max_states, max_transitions=max_transitions)
                if answer['status'] == 'YES':
                    w = (answer['word'] if cert['code'] == 'paired'
                         else ''.join(u+'0' for u in answer['blocks']))
                    assert witness(I, w) and border_witness(I, w)
                    return dict(status='YES', word=w, blocks=answer['blocks'],
                                slices=rows, schemas=total_schemas, convolution=answer,
                                delimiter_edges=seq)
                if answer['status'] != 'NO':
                    unresolved = True
                    row['capped_schema'] = True
    if unresolved:
        return dict(status='UNKNOWN', reason='Uncertified slice or incomplete finite search',
                    slices=rows, schemas=total_schemas)
    return dict(status='NO', reason='Every certified complete schema cover is empty',
                slices=rows, schemas=total_schemas)

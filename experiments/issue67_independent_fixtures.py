#!/usr/bin/env python3
"""Issue #67: literal oracles, scoped complete unions and honest coverage receipts.

Only this harness is new. Production modules are imported byte-for-byte.
The S-only union projection has a written, fixture-specific completeness proof;
it is NOT described as exhaustion of the original unpruned enumerator.
No Lean execution or all-input theorem is inferred from these tests.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import asdict, is_dataclass
import hashlib
from itertools import product
import json
import os
from pathlib import Path
import platform
import resource
import signal
import subprocess
import sys
import time

from border_lab import Instance
import rank_preimage as compiler
from rank_preimage_core import Atom, Budget, Exhausted, Query, fld, table
from rank_query_graphs import Colour, Graph, finish_on_graph, graph_from_reference
from rank_query_prefix import Reference

BASE = '19b06d4fed9da635d9b911f0e908d04e4fc4b099'
PINS = {
    'border_lab.py': '1144ae52379e0417772e79582269cacd91c5bc17',
    'rank_query_prefix.py': '135d3cb960d07dfddefd74dd255bba289a08af1b',
    'rank_query_graphs.py': '6fcc612e47ef65edbb7ec9ff973a528a422da8e4',
    'rank_preimage_core.py': 'fe297ab4f2252468b1734f6885765cde0d2cecb9',
    'rank_preimage.py': '852fa7d7ba199b9d91ab24a8f7b5abf29ed8819b',
}
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_receipt():
    files = {}
    for name, expected in PINS.items():
        raw = (HERE / name).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if actual != expected:
            raise ValueError(f'Source pin mismatch: {name}: {actual} != {expected}')
        files[name] = {'git_blob': actual, 'sha256': hashlib.sha256(raw).hexdigest()}
    return files


def instance(data):
    return Instance(tuple(tuple(row) for row in data['delta']), frozenset(data['final']),
                    frozenset(tuple(pair) for pair in data.get('flags', [])),
                    frozenset(data.get('bad', [])), data.get('start', 0))


def dag_bound(I):
    """All-state DAG check, not only initial-state reachability.

    A reverse path is the reversal of a path in this DAG. Thus its length is
    at most this maximum. No timeout or guessed word cutoff enters the bound.
    """
    colour, heights = [0] * len(I.delta), {}
    def visit(q):
        if colour[q] == 1:
            raise ValueError('The complete small oracle requires an acyclic instance')
        if colour[q] == 2:
            return heights[q]
        colour[q] = 1
        h = 0
        for target in I.delta[q]:
            if target >= 0:
                h = max(h, 1 + visit(target))
        colour[q] = 2
        heights[q] = h
        return h
    return max((visit(q) for q in range(len(I.delta))), default=0)


def literal_witness(I, word):
    """Forward cut/suffix predicate; no production run/witness/border methods."""
    states = [I.start]
    for letter in word:
        target = I.delta[states[-1]][int(letter)]
        if target < 0:
            return False, {'undefined': True}
        states.append(target)
    flags = [(i, j) for j in range(len(word) + 1) for i in range(j + 1)
             if word[i:].startswith(word[j:]) and (states[i], states[j]) in I.flags]
    good = states[-1] in I.final and not any(q in I.bad for q in states) and not flags
    return good, {'states': states, 'flagged_cuts': flags,
                  'diagonal_cuts': [(i, j) for i, j in flags if i == j],
                  'empty_suffix_cuts': [(i, j) for i, j in flags if j == len(word)]}


def complete_words(I):
    bound = dag_bound(I)
    words, todo = [], [('', I.start)]
    while todo:
        word, q = todo.pop()
        assert len(word) <= bound
        words.append(word)
        for bit in (1, 0):
            target = I.delta[q][bit]
            if target >= 0:
                todo.append((word + str(bit), target))
    return words, bound


def literal_safe(I, B):
    if len(B.labels) != len(B.word) + 1 or B.labels[0] not in I.final:
        return False
    if any(q in I.bad for q in B.labels):
        return False
    for j, bit in enumerate(B.word):
        if I.delta[B.labels[j + 1]][int(bit)] != B.labels[j]:
            return False
    for j in range(len(B.word) + 1):
        for b in range(j + 1):
            if B.word[:j].endswith(B.word[:b]) and (B.labels[j], B.labels[b]) in I.flags:
                return False
    return True


def all_continuations(I, B):
    bound = dag_bound(I)
    if not literal_safe(I, B):
        return []
    todo, answer = [B], []
    while todo:
        C = todo.pop()
        assert len(C.word) <= bound
        answer.append(C)
        for p in reversed(range(len(I.delta))):
            for bit in (1, 0):
                if I.delta[p][bit] == C.labels[-1]:
                    D = Reference(C.word + str(bit), C.labels + (p,))
                    if literal_safe(I, D):
                        todo.append(D)
    return answer


def return_offsets(B, C):
    return [i for i in range(1, len(C.word) - len(B.word) + 1)
            if C.word[i:i + len(B.word)] == B.word]


def first_return(B, C):
    return (bool(B.word) and len(C.word) > len(B.word) and C.word.startswith(B.word)
            and C.labels[:len(B.labels)] == B.labels
            and return_offsets(B, C) == [len(C.word) - len(B.word)])


def complete_first_returns(I, B):
    return [C for C in all_continuations(I, B) if first_return(B, C)]


def literal_finish(I, B):
    return [C for C in all_continuations(I, B)
            if C.labels[-1] == I.start and not return_offsets(B, C)]


def literal_graph(I, B):
    """Rebuild all edges/colours using direct string tests, no KMP recurrence."""
    colours, edges = [], set()
    n = len(B.word)
    for j in range(n + 1):
        prefix = B.word[:j]
        borders = [b for b in range(j + 1) if prefix.endswith(B.word[:b])]
        forbidden = sum(1 << p for p in range(len(I.delta))
                        if any((p, B.labels[b]) in I.flags for b in borders))
        colours.append(Colour(B.labels[j], forbidden, B.word[j] if j < n else '', j == 0, j == n))
        edges.add((j, 'F', max((b for b in borders if b < j), default=0)))
        if j < n:
            edges.add((j, 'S', j + 1))
        for bit in '01':
            candidates = [b for b in range(n + 1) if (prefix + bit).endswith(B.word[:b])]
            edges.add((j, 'K' + bit, max(candidates)))
    return Graph(tuple(colours), frozenset(edges))


def literal_test(test, colour):
    kind, args = test.kind, test.args
    if kind == 'true':
        return True
    if kind == 'false':
        return False
    if kind == 'field':
        return getattr(colour, args[0]) == args[1]
    if kind == 'and':
        return all(literal_test(t, colour) for t in args)
    if kind == 'not':
        return not literal_test(args[0], colour)
    raise ValueError('Independent input oracle does not silently delegate: ' + kind)


def literal_accepts(G, observer, source, target):
    if observer.kind != 'table':
        raise ValueError('Independent query oracle is deliberately table-only')
    predicates, transitions = observer.data
    todo = deque((source, q) for q in observer.initial
                 if literal_test(predicates[q], G.colours[source]))
    seen = set(todo)
    while todo:
        v, q = todo.popleft()
        if v == target and q in observer.final:
            return True
        for a, label, b in transitions:
            if a != q:
                continue
            for u, edge, w in G.edges:
                node = (w, b)
                if (u == v and edge == label and node not in seen
                        and literal_test(predicates[b], G.colours[w])):
                    seen.add(node)
                    todo.append(node)
    return False


def literal_truth(G, Q, assignment=None):
    assignments = [tuple(assignment[v] for v in Q.variables)] if assignment is not None else product(range(len(G.colours)), repeat=len(Q.variables))
    for values in assignments:
        d = dict(zip(Q.variables, values))
        if any(not literal_test(t, G.colours[d[v]]) for v, t in Q.tests):
            continue
        if any(d[x] != d[y] for x, y in Q.equal) or any(d[x] == d[y] for x, y in Q.unequal):
            continue
        if all(literal_accepts(G, a.observer, d[a.source], d[a.target]) for a in Q.atoms):
            return True
    return False


def shared_query(length):
    exact = table(length + 1, tuple((i, 'S', i + 1) for i in range(length)), final=(length,))
    odd = table(2, ((0, 'S', 1), (1, 'S', 0)), final=(1,))
    return Query(('r', 'e'), (('r', fld('root', True)), ('e', fld('end', True))),
                 atoms=(Atom(exact, 'r', 'e'), Atom(odd, 'r', 'e')))


def wrap_query(positive):
    return Query(('e', 'u'), (('e', fld('end', True)), ('u', fld('end', True))),
                 equal=(('e', 'u'),) if positive else (),
                 unequal=() if positive else (('e', 'u'),),
                 atoms=(Atom(table(1, ()), 'e', 'u'),
                        Atom(table(2, ((0, 'K0', 1),), final=(1,)), 'e', 'u')))


def s_only_diagrams(I, Q):
    """Complete *satisfiable-shape* projection for these root/end S-only queries.

    Proof in the note: illegal portals reject; root is core; end is last fresh;
    hence core/enter-S/forward is the only possible shape for each atom.
    Both weak orders of FIRST and LAST and all legal finite labels/controls
    are enumerated. This is not a sampled prefix of iter_diagrams.
    """
    assert Q.variables == ('r', 'e') and not Q.equal and not Q.unequal
    assert Q.tests == (('r', fld('root', True)), ('e', fld('end', True)))
    choices = []
    for a in Q.atoms:
        o = a.observer
        assert (a.source, a.target) == ('r', 'e') and o.kind == 'table'
        assert all(t.kind == 'true' for t in o.data[0])
        assert all(label == 'S' for _, label, _ in o.data[1])
        choices.append([(start, p, q, final) for start in o.initial for final in sorted(o.final)
                        for p, label, q in o.data[1]])
    for bit in '01':
        for ai, atom in enumerate(Q.atoms):
            shape = next(compiler.path_shapes(ai, atom.observer.size, ('core', 'o:r'),
                                             ('fresh', 'n:e'), bit, Budget()))
            assert tuple((p.kind, p.label) for p in shape) == (('core', ''), ('enter', 'S'), ('forward', ''))
        for groups in (((compiler.FIRST, compiler.LAST, 'n:e'),),
                       ((compiler.FIRST,), (compiler.LAST, 'n:e'))):
            for controls in product(*choices):
                pieces = tuple((compiler.Piece('core', 'o:r', compiler.END, a, b),
                                compiler.Piece('enter', compiler.END, compiler.FIRST, b, c, 'S'),
                                compiler.Piece('forward', compiler.FIRST, 'n:e', c, d))
                               for a, b, c, d in controls)
                for states in product(range(len(I.delta)), repeat=len(groups)):
                    p = states[0]
                    q = I.delta[p][int(bit)]
                    if q < 0 or p in I.bad or q in I.bad or (p, p) in I.flags:
                        continue
                    for middle_bits in product('01', repeat=len(groups) - 1):
                        for mask in range(1 << len(I.delta)):
                            if mask >> q & 1:
                                continue
                            yield compiler.Diagram((('r', 'core', 'o:r'), ('e', 'fresh', 'n:e')),
                                                   groups, states, middle_bits + ('',), bit,
                                                   Colour(q, mask, '', False, True), pieces)


class Trace:
    """Observational provenance; no production function replacement.

    Generator profile events count resumptions as well as initial calls and
    are labelled events. Compile-return depths follow actual query objects,
    not the configured recursion bound or the witness's maximum rank.
    """
    def __init__(self):
        self.calls, self.depths, self.compiled_depths = Counter(), {}, Counter()
        self.decider_success_depths = []
        self.interval_moves, self.interval_paths = Counter(), Counter()
        self.previous = None

    def profile(self, frame, event, value):
        name = frame.f_code.co_name
        filename = frame.f_code.co_filename.rsplit('/', 1)[-1]
        if filename not in ('rank_preimage.py', 'rank_preimage_core.py'):
            return
        if event == 'call' and name in ('decide', 'iter_rank_queries', 'preimages', 'compile_diagram',
                                        'extract_diagram', 'reconstruct_reference', 'finish_queries', 'model'):
            self.calls[name] += 1
        if event != 'return':
            return
        if name == 'move':
            observer = frame.f_locals.get('self')
            if observer is not None and getattr(observer, 'kind', None) == 'interval':
                active = len(observer.data[1])
                self.interval_moves[str(active) + (':nonempty' if value else ':empty')] += 1
        elif name == 'path':
            observer = frame.f_locals.get('o')
            if observer is not None and getattr(observer, 'kind', None) == 'interval':
                active = len(observer.data[1])
                self.interval_paths[str(active) + (':yes' if value is not None else ':no')] += 1
        if name == 'finish_queries' and isinstance(value, Query):
            self.depths[id(value)] = 0
        elif name == 'compile_diagram' and isinstance(value, Query):
            depth = self.depths.get(id(frame.f_locals['query']), 0) + 1
            self.depths[id(value)] = depth
            self.compiled_depths[depth] += 1
        elif name == 'model' and isinstance(value, compiler.Model):
            parent = frame.f_back
            if parent is not None and parent.f_code.co_name == 'decide' and parent.f_code.co_filename.rsplit('/', 1)[-1] == 'rank_preimage.py':
                self.decider_success_depths.append(self.depths.get(id(frame.f_locals['Q']), 0))

    def __enter__(self):
        self.previous = sys.getprofile()
        sys.setprofile(self.profile)
        return self

    def __exit__(self, *_):
        sys.setprofile(self.previous)

    def receipt(self):
        return {'profile_events': dict(self.calls), 'compiled_depth_counts': dict(self.compiled_depths),
                'max_compiled_depth': max(self.compiled_depths, default=0),
                'automatic_decider_success_depths': self.decider_success_depths,
                'interval_move_return_events': dict(self.interval_moves),
                'interval_path_results': dict(self.interval_paths)}


def certificate(I, B, C, Q):
    sol = compiler.model(literal_graph(I, C), Q)
    assert sol is not None
    D = compiler.extract_diagram(I, B, C, Q, sol)
    P = compiler.compile_diagram(I, Q, D)
    base_sol = compiler.model(literal_graph(I, B), P)
    assert base_sol is not None
    reconstructed, assignment = compiler.reconstruct_reference(I, B, D, P, base_sol)
    assert literal_safe(I, reconstructed) and first_return(B, reconstructed)
    return P, D, reconstructed, assignment


def terminal_case(case, out):
    I = instance(case['instance'])
    words, bound = complete_words(I)
    evidence = {w: literal_witness(I, w) for w in words}
    found = [w for w, (yes, _) in evidence.items() if yes]
    assert bool(found) == case['expected']
    import border_lab
    assert all(border_lab.witness(I, w) == yes and border_lab.border_witness(I, w) == yes
               for w, (yes, _) in evidence.items())
    out.update(oracle_bound=bound, oracle_words=words, oracle_witnesses=found,
               oracle_details=evidence, semantic_answer=bool(found))
    if bound < 2:
        with Trace() as trace:
            answer = compiler.decide(I, max_work=100000)
        assert answer['status'] == ('YES' if case['expected'] else 'NO')
        out.update(backend_answer=answer, coverage=trace.receipt(),
                   coverage_class='automatic_python_decider_boundary_or_zero_promotion')
        return
    B = Reference('0', (3, 2))
    refs = all_continuations(I, B)
    finish = []
    for C in refs:
        graph = literal_graph(I, C)
        assert graph == graph_from_reference(I, C)
        expected = bool(literal_finish(I, C))
        formula = any(compiler.model(graph, Q) is not None for Q in compiler.finish_queries(I))
        assert expected == formula == (finish_on_graph(I, graph) is not None)
        finish.append({'reference': asdict(C), 'finish': expected})
    out['finishing_checks'] = finish
    out['coverage_class'] = 'complete_DAG_oracle_and_original_finishing_components'
    if case['expected']:
        B1, B2, B3 = [Reference('0' * n, tuple(range(3, 2 - n, -1))) for n in (1, 2, 3)]
        assert [bool(literal_finish(I, C)) for C in (B1, B2, B3)] == [False, False, True]
        assert complete_first_returns(I, B1) == [B2]
        assert complete_first_returns(I, B2) == [B3]
        with Trace() as trace:
            Q = next(q for q in compiler.finish_queries(I) if compiler.model(literal_graph(I, B3), q) is not None)
            P1, D1, C3, _ = certificate(I, B2, B3, Q)
            P2, D2, C2, _ = certificate(I, B1, B2, P1)
            assert C2 == B2 and C3 == B3
            # Replay both stages from the final base formula, not two unrelated models.
            sol2 = compiler.model(literal_graph(I, B1), P2)
            R2, assignment2 = compiler.reconstruct_reference(I, B1, D2, P2, sol2)
            assert R2 == B2 and compiler.verify_assignment(literal_graph(I, R2), P1, assignment2)
            sol1 = compiler.model(literal_graph(I, R2), P1)
            R3, assignment1 = compiler.reconstruct_reference(I, R2, D1, P1, sol1)
            assert R3 == B3 and compiler.verify_assignment(literal_graph(I, R3), Q, assignment1)
            assert literal_witness(I, R3.word[::-1])[0]
        out.update(coverage_class='certificate_directed_two_promotion_compiler_replay',
                   coverage=trace.receipt(), semantic_minimum_promotions=2,
                   automatic_two_promotion_decision='NOT_ESTABLISHED',
                   chain=[asdict(B1), asdict(B2), asdict(B3)],
                   diagrams=[asdict(D2), asdict(D1)],
                   singleton_role_groups=[D2.groups, D1.groups],
                   overlap={'base': '00', 'extension': '000', 'occurrence_starts': [0, 1], 'overlap_length': 1})
        assert trace.receipt()['max_compiled_depth'] == 2


def shared_case(case, out):
    I = instance(case['instance'])
    B = Reference(case['base']['word'], tuple(case['base']['labels']))
    Q = shared_query(case['exact_length'])
    refs = complete_first_returns(I, B)
    assert sorted(C.word for C in refs) == case['expected_first_returns']
    single = []
    for atom in Q.atoms:
        one = Query(Q.variables, Q.tests, atoms=(atom,))
        single.append(any(literal_truth(literal_graph(I, C), one) for C in refs))
    truth = {C.word: literal_truth(literal_graph(I, C), Q) for C in refs}
    assert single == case['expected_singles'] and any(truth.values()) == case['expected']
    for C in refs:
        graph = literal_graph(I, C)
        assert graph == graph_from_reference(I, C)
        assert truth[C.word] == (compiler.model(graph, Q) is not None)
    out.update(oracle_bound=dag_bound(I), all_first_returns=[asdict(C) for C in refs],
               independent_truth=truth, independent_singles=single,
               split_generator_mutant_answer=all(single), semantic_answer=case['expected'],
               coverage_class='complete_S_only_satisfiable_shape_compiler_union',
               original_unpruned_enumerator_exhausted=False,
               projection_proof='All omitted role/order/portal/control classes have an unsatisfiable original compiled clause.')
    counts = Counter(candidate_diagrams=0, rejected_diagrams=0, compiled_clauses=0, satisfied_clauses=0)
    observed = set()
    completed_witnesses = set()
    group_counts = Counter()
    active_counts = Counter()
    out['union_counts'] = counts
    with Trace() as trace:
        for D in s_only_diagrams(I, Q):
            counts['candidate_diagrams'] += 1
            try:
                P = compiler.compile_diagram(I, Q, D)
            except (compiler.InvalidDiagram, KeyError):
                counts['rejected_diagrams'] += 1
                continue
            counts['compiled_clauses'] += 1
            sol = compiler.model(literal_graph(I, B), P)
            if sol is None:
                continue
            counts['satisfied_clauses'] += 1
            C, assignment = compiler.reconstruct_reference(I, B, D, P, sol)
            assert literal_safe(I, C) and first_return(B, C)
            assert C in refs and literal_truth(literal_graph(I, C), Q, assignment)
            observed.add(C.word)
            completion = finish_on_graph(I, literal_graph(I, C))
            assert completion is not None
            extra, labels = completion
            full = Reference(C.word + extra, C.labels + labels)
            assert literal_safe(I, full) and literal_witness(I, full.word[::-1])[0]
            completed_witnesses.add(full.word[::-1])
            group_counts[len(D.groups)] += 1
            for atom in P.atoms:
                if atom.observer.kind == 'interval':
                    active_counts[len(atom.observer.data[1])] += 1
    assert bool(counts['satisfied_clauses']) == case['expected']
    assert observed == {word for word, yes in truth.items() if yes}
    if case['expected']:
        assert group_counts[2] > 0 and active_counts[2] > 0
    else:
        assert all(single) and not observed  # The split-generator mutant is killed.
    assert any(key.startswith('2:') for key in trace.interval_moves)
    out.update(projected_union_status='EXHAUSTED', reconstructed_words=sorted(observed),
               completed_original_witnesses=sorted(completed_witnesses), coverage=trace.receipt(),
               satisfied_mark_group_counts=dict(group_counts), satisfied_interval_observer_counts=dict(active_counts))


def wrap_case(case, out):
    I = instance(case['instance'])
    B = Reference(case['base']['word'], tuple(case['base']['labels']))
    Q = wrap_query(case['expected'])
    refs = complete_first_returns(I, B)
    assert [C.word for C in refs] == ['000']
    found = [C for C in refs if literal_truth(literal_graph(I, C), Q)]
    assert bool(found) == case['expected']
    assert all(literal_truth(literal_graph(I, C), Q) == (compiler.model(literal_graph(I, C), Q) is not None) for C in refs)
    out.update(oracle_bound=dag_bound(I), all_first_returns=[asdict(C) for C in refs], semantic_answer=bool(found),
               coverage_class='literal_coincidence_oracle_and_compiler_certificate', full_union_exhausted=False)
    if found:
        with Trace() as trace:
            P, D, C, assignment = certificate(I, B, found[0], Q)
            assert literal_truth(literal_graph(I, C), Q, assignment)
        assert len(D.groups) == 1 and compiler.FIRST in D.groups[0] and compiler.LAST in D.groups[0]
        assert any(piece.kind == 'wrap' for pieces in D.pieces for piece in pieces)
        out.update(coverage=trace.receipt(), diagram=asdict(D), reconstructed=asdict(C), assignment=assignment)


def raw_union(case, out, maximum):
    I = instance(case['instance'])
    B = Reference(case['base']['word'], tuple(case['base']['labels']))
    Q = shared_query(case['exact_length']) if case['family'] == 'shared_union' else wrap_query(case['expected'])
    budget, counts = Budget(maximum), Counter(candidate_diagrams=0, rejected_diagrams=0, compiled_clauses=0, satisfied_clauses=0)
    out.update(oracle_answer=case['expected'], union_counts=counts, work_limit=maximum,
               coverage_class='original_unpruned_Python_compiler_union')
    try:
        for D in compiler.iter_diagrams(I, Q, budget):
            budget.tick()
            counts['candidate_diagrams'] += 1
            try:
                P = compiler.compile_diagram(I, Q, D)
            except (compiler.InvalidDiagram, KeyError):
                counts['rejected_diagrams'] += 1
                continue
            counts['compiled_clauses'] += 1
            sol = compiler.model(literal_graph(I, B), P, budget)
            if sol is not None:
                counts['satisfied_clauses'] += 1
                C, assignment = compiler.reconstruct_reference(I, B, D, P, sol)
                assert literal_safe(I, C) and first_return(B, C)
                assert literal_truth(literal_graph(I, C), Q, assignment)
        assert bool(counts['satisfied_clauses']) == case['expected']
        out.update(status='EXHAUSTED', full_union_exhausted=True)
    except Exhausted:
        out.update(status='UNKNOWN', reason='work_limit', full_union_exhausted=False)
    finally:
        out['work_used'] = budget.used


def automatic(case, out, maximum):
    I = instance(case['instance'])
    trace = Trace()
    out.update(coverage_class='original_Python_whole_terminal_decider', oracle_answer=case['expected'])
    try:
        with trace:
            result = compiler.decide(I, max_work=maximum, reconstruct_limit=100000)
        out['backend_answer'] = result
        if result['status'] == 'UNKNOWN':
            out.update(status='UNKNOWN', reason=result.get('reason'))
        else:
            assert (result['status'] == 'YES') == case['expected']
            if result['status'] == 'YES':
                assert literal_witness(I, result['word'])[0]
            out['status'] = 'COMPLETED'
    finally:
        out['coverage'] = trace.receipt()


def child(args, case):
    start = time.perf_counter()
    usage = resource.getrusage(resource.RUSAGE_SELF)
    out = {'id': case['id'], 'job': args.job.split(':', 1)[0], 'input_sha256': digest(case), 'status': 'RUNNING'}
    def timeout(*_):
        raise TimeoutError('wall_limit')
    signal.signal(signal.SIGALRM, timeout)
    resource.setrlimit(resource.RLIMIT_CPU, (args.cpu_seconds, args.cpu_seconds + 1))
    memory = args.memory_mib * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
    try:
        signal.setitimer(signal.ITIMER_REAL, args.wall_seconds)
        source_receipt()
        if out['job'] == 'strict':
            {'terminal': terminal_case, 'shared_union': shared_case, 'wrap': wrap_case}[case['family']](case, out)
            out['status'] = 'PASS'
        elif out['job'] == 'raw':
            raw_union(case, out, args.max_work)
        elif out['job'] == 'automatic':
            automatic(case, out, args.max_work)
        else:
            raise ValueError('Unknown job kind')
    except (TimeoutError, MemoryError, RecursionError, OverflowError) as exc:
        out.update(status='UNKNOWN', reason=type(exc).__name__ + ': ' + str(exc))
    except Exception as exc:
        import traceback
        out.update(status='FAIL', reason=type(exc).__name__ + ': ' + str(exc), traceback=traceback.format_exc())
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        final = resource.getrusage(resource.RUSAGE_SELF)
        out['resources'] = {'wall_seconds': time.perf_counter() - start,
                            'cpu_user_seconds': final.ru_utime - usage.ru_utime,
                            'cpu_system_seconds': final.ru_stime - usage.ru_stime,
                            'peak_rss_kib': ((final.ru_maxrss + 1023) // 1024 if sys.platform == 'darwin' else final.ru_maxrss)}
        out['limits'] = {'wall_seconds': args.wall_seconds, 'cpu_seconds': args.cpu_seconds,
                         'memory_mib': args.memory_mib, 'max_work_for_stress': args.max_work}
    print(json.dumps(out, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures', type=Path, default=ROOT / 'tests/fixtures/issue67-independent/cases.json')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--mode', choices=('strict', 'stress'), default='strict')
    parser.add_argument('--job', help=argparse.SUPPRESS)
    parser.add_argument('--only')
    parser.add_argument('--wall-seconds', type=float, default=60)
    parser.add_argument('--cpu-seconds', type=int, default=55)
    parser.add_argument('--memory-mib', type=int, default=1024)
    parser.add_argument('--max-work', type=int, default=100000)
    parser.add_argument('--seed', type=int, default=2026092067)
    parser.add_argument('--snapshot-kind', choices=('full-checkout', 'partial-connector'), default='full-checkout')
    args = parser.parse_args()
    data = json.loads(args.fixtures.read_text())
    if data.get('schema') != 1 or data.get('source_revision') != BASE:
        raise ValueError('Fixture schema/source revision mismatch')
    cases = {case['id']: case for case in data['cases']}
    if len(cases) != len(data['cases']):
        raise ValueError('Duplicate fixture identifier')
    if args.job:
        child(args, cases[args.job.split(':', 1)[1]])
        return
    if args.output is None:
        parser.error('--output is required; use an isolated output path')
    pins = source_receipt()
    if args.mode == 'strict':
        jobs = [('strict', name) for name in cases]
    else:
        jobs = [('automatic', name) for name in ('two-promotions-positive', 'two-promotions-ordered-negative')]
        jobs += [('raw', name) for name in cases if cases[name]['family'] in ('shared_union', 'wrap')]
    if args.only:
        jobs = [(kind, name) for kind, name in jobs if name == args.only]
    if not jobs:
        parser.error('No selected jobs')
    command = [sys.executable, str(Path(__file__).resolve()), '--fixtures', str(args.fixtures.resolve()),
               '--wall-seconds', str(args.wall_seconds), '--cpu-seconds', str(args.cpu_seconds),
               '--memory-mib', str(args.memory_mib), '--max-work', str(args.max_work)]
    env = dict(os.environ, PYTHONHASHSEED=str(args.seed), PYTHONDONTWRITEBYTECODE='1')
    rows = []
    for kind, name in jobs:
        invocation = command + ['--job', kind + ':' + name]
        print(f'{kind}: {name}', file=sys.stderr, flush=True)
        began = time.perf_counter()
        try:
            run = subprocess.run(invocation, capture_output=True, text=True, env=env, timeout=args.wall_seconds + 5)
            if run.returncode or not run.stdout.strip():
                resource_exit = run.returncode in (-signal.SIGXCPU, -signal.SIGKILL, -signal.SIGALRM)
                row = {'id': name, 'job': kind, 'status': 'UNKNOWN' if resource_exit else 'FAIL', 'reason': 'child_exit',
                       'returncode': run.returncode, 'stderr': run.stderr, 'stdout': run.stdout}
            else:
                row = json.loads(run.stdout)
        except subprocess.TimeoutExpired:
            row = {'id': name, 'job': kind, 'status': 'UNKNOWN', 'reason': 'parent_wall_limit'}
        row['command'] = invocation
        row['parent_observed_wall_seconds'] = time.perf_counter() - began
        row['python_hash_seed'] = args.seed
        rows.append(row)
        # Preserve completed observations even if the parent is interrupted.
        args.output.parent.mkdir(parents=True, exist_ok=True)
        checkpoint = {'schema': 1, 'mode': args.mode, 'status': 'INCOMPLETE',
                      'source_revision': BASE, 'rows': rows, 'planned_jobs': len(jobs)}
        args.output.write_text(json.dumps(checkpoint, indent=2, sort_keys=True) + '\n')
    statuses = Counter(row['status'] for row in rows)
    good = all(row['status'] == 'PASS' for row in rows) if args.mode == 'strict' else not statuses['FAIL']
    try:
        local_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        local_head = None
    report = {'schema': 1, 'mode': args.mode, 'status': ('PASS' if good else 'FAIL') if args.mode == 'strict' else ('DIAGNOSTIC' if good else 'DIAGNOSTIC_WITH_FAILURES'),
              'source_revision': BASE, 'snapshot_kind': args.snapshot_kind, 'local_checkout_head': local_head,
              'command': [sys.executable, *sys.argv], 'seed': args.seed, 'random_search_used': False,
              'source_files': pins, 'harness_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'fixtures_sha256': hashlib.sha256(args.fixtures.read_bytes()).hexdigest(),
              'environment': {'python': sys.version, 'platform': platform.platform(), 'cpu_count': os.cpu_count(),
                              'rss_units': 'KiB normalized; peak over the entire child process, not an allocation delta'},
              'native_lean': 'NOT_RUN', 'original_expression_C081_frontend': 'NOT_RUN',
              'automatic_two_promotion_success': any(2 in row.get('coverage', {}).get('automatic_decider_success_depths', []) for row in rows),
              'statuses': dict(statuses), 'rows': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': report['status'], 'statuses': dict(statuses), 'output': str(args.output)}, sort_keys=True))
    if not good:
        raise SystemExit(1)


if __name__ == '__main__':
    main()

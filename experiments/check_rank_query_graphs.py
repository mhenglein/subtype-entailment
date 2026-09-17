#!/usr/bin/env python3
"""Independent graph, portal and shared-observer audits of a CANDIDATE proof.

No full backward query-elimination compiler or unrestricted decision is run.
Finite tests are not a proof of the general syntactic closure lemma.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import random
from border_lab import Instance, words, witness, border_witness
from rank_query_prefix import Reference, prefix_function, ranks_and_milestones, valid_reverse_prefix, layer_graph
from rank_query_graphs import (Automaton, Colour, Graph, EDGE_LABELS,
    graph_from_reference, literal_graph, first_return, local_extension,
    finish_on_graph, classify_edge, query_path, path_diagram, forward_observer, exact_edge_word)
from modular_sync_family import make_family

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026091531


def random_observer(rng, size):
    transitions = frozenset((q, a, p) for q in range(size) for a in EDGE_LABELS
                            for p in range(size) if rng.random() < .30)
    predicates = []
    for q in range(size):
        choice = rng.randrange(9)
        predicates.append((('root', False),) if choice == 0 else
                          (('end', False),) if choice == 1 else ())
    return Automaton(size, 0, frozenset(q for q in range(size) if rng.random() < .6),
                     transitions, tuple(predicates))


def check():
    rng = random.Random(SEED)
    count = Counter()
    samples = []
    # Pure prefix-graph identities for every word in this finite range. Cut
    # labels/flags are deliberately arbitrary; the structural identity is word-theoretic.
    selected = []
    for n in range(1, 12):
        for bits in product('01', repeat=n):
            Cword = ''.join(bits)
            k = 2 + n % 4
            labels = tuple(rng.randrange(k) for _ in range(n + 1))
            flags = frozenset((p, q) for p in range(k) for q in range(k) if rng.random() < .25)
            I = Instance(tuple((0, 0) for _ in range(k)), frozenset(), flags)
            C = Reference(Cword, labels)
            direct = graph_from_reference(I, C)
            assert direct == literal_graph(I, C)
            count['direct_literal_graphs'] += 1
            for m in range(1, n):
                if not first_return(Cword[:m], Cword):
                    continue
                B = Reference(Cword[:m], labels[:m + 1])
                graph, origins = local_extension(I, B, C, require_safe=False)
                assert graph == direct, (Cword, m)
                assert origins[:-1] == tuple(prefix_function(Cword)[m + 1:n])
                count['all_first_return_extensions'] += 1
                for edge in graph.edges:
                    classify_edge(m, n, edge)
                    count['classified_edges'] += 1
                # Exact old-core change: ONLY old endpoint match edge and colour change.
                base = graph_from_reference(I, B)
                induced = frozenset(e for e in graph.edges if e[0] <= m and e[2] <= m)
                expected = frozenset(e for e in base.edges
                                     if not (e[0] == m and e[1] == 'K' + Cword[m]))
                assert induced == expected
                count['old_core_edge_equalities'] += 1
                if len(selected) < 300 or rng.random() < .025:
                    selected.append((I, B, C, graph))
    # Arbitrary finite path observers, not only witness matching. We audit the
    # entry bound and joint physical endpoint marks required by query diagrams.
    rng.shuffle(selected)
    for I, B, C, graph in selected[:400]:
        m, n = len(B.word), len(C.word)
        observers = [random_observer(rng, rng.randrange(1, 5)) for _ in range(4)]
        marked_union = set()
        for A in observers:
            for _ in range(8):
                u, v = rng.randrange(n + 1), rng.randrange(n + 1)
                path = query_path(graph, A, u, v)
                count['regular_path_queries'] += 1
                if path is not None:
                    diagram = path_diagram(graph, m, A, u, v, path)
                    marked_union.update(diagram['marked_positions'])
                    count['positive_diagram_certificates'] += 1
                    count['compressed_path_pieces'] += len(diagram['pieces'])
                    for piece in diagram['pieces']:
                        if piece['kind'] != 'forward':
                            continue
                        l, q = piece['start']; r, p = piece['end']
                        assert p in forward_observer(graph, A, l, r, frozenset({q}))
                        count['observed_shared_forward_pieces'] += 1
            l, r = sorted((rng.randrange(m + 1, n + 1), rng.randrange(m + 1, n + 1)))
            only_forward = frozenset((u, a, v) for u, a, v in graph.edges
                                     if l <= u < v <= r and v == u + 1)
            streamed = bool(forward_observer(graph, A, l, r) & A.finals)
            literal = query_path(graph, A, l, r, only_forward) is not None
            assert streamed == literal
            count['forward_stream_product_oracles'] += 1
        assert len(marked_union) <= 2 + sum(8 * (2 * (A.size + 1) + 4) for A in observers)
    # The output at the final reference endpoint cannot use an ordinary fresh
    # mismatch-to-core rule: its K transition can WRAP to first fresh position.
    endpoint_rows = []
    I = Instance(((0, 0),), frozenset())
    for n in range(1, 8):
        B = Reference('0' * n, (0,) * (n + 1))
        C = Reference('0' * (n + 1), (0,) * (n + 2))
        G, _ = local_extension(I, B, C, require_safe=False)
        assert G.target(G.end, 'K0') == n + 1 == G.end
        endpoint_rows.append({'base_length': n, 'fresh_vertices': 1, 'wrap_is_self_loop': True})
        count['overlapping_one_vertex_extensions'] += 1
    # Converse failure is NOT in the proof's query alphabet. It introduces
    # arbitrarily many core-to-fresh entries and invalidates the portal bound.
    converse_rows = []
    for n in range(1, 10):
        B = Reference('0', (0, 0))
        C = Reference('0' + '1' * n + '0', (0,) * (n + 3))
        G, _ = local_extension(I, B, C, require_safe=False)
        targets = {u for u, a, v in G.edges if a == 'F' and v == 0 and u > 1}
        assert len(targets) == n
        converse_rows.append({'ones': n, 'inverse_failure_entries_from_root': len(targets)})
    # A single shared strip cannot satisfy two incompatible exact observations.
    B = Reference('0', (0, 0))
    A0 = exact_edge_word(('K0',))
    A10 = exact_edge_word(('K1', 'K0'))
    individual = [False, False]
    joint = False
    for n in range(1, 10):
        C = Reference('0' + '1' * n + '0', (0,) * (n + 3))
        G, _ = local_extension(I, B, C, require_safe=False)
        vals = [bool(forward_observer(G, A, 2, G.end) & A.finals) for A in (A0, A10)]
        individual = [x or y for x, y in zip(individual, vals)]
        joint |= all(vals)
        count['shared_assignment_guard_cases'] += 1
    assert individual == [True, True] and not joint
    # Exact witness query versus original forward/reversed predicates. The path
    # itself is supplied here; no unbounded query-preimage compiler is invoked.
    for trial in range(240):
        k = rng.randrange(2, 8)
        finals = frozenset({k - 1})
        delta = tuple(tuple(rng.randrange(-1, k) for _ in range(2)) for _ in range(k - 1)) + ((-1, -1),)
        flags = frozenset((p, q) for p in range(k) for q in range(k) if rng.random() < .06)
        bad = frozenset(q for q in range(k) if rng.random() < .015)
        I = Instance(delta, finals, flags, bad, rng.randrange(k))
        for w in words('01', 8):
            count['original_word_comparisons'] += 1
            ok = witness(I, w)
            assert ok == border_witness(I, w)
            run = I.run(w)
            if not w or run is None or run[-1] not in finals:
                continue
            rho, labels = w[::-1], tuple(reversed(run))
            assert valid_reverse_prefix(I, rho, labels) == ok
            if not ok:
                continue
            count['accepted_witness_hierarchies'] += 1
            depths, milestones = ranks_and_milestones(rho)
            assert max(depths) <= k - 1
            refs = [Reference(rho[:j], labels[:j + 1]) for j in milestones]
            G = graph_from_reference(I, refs[0])
            for B, C in zip(refs, refs[1:]):
                G, _ = local_extension(I, B, C)
                assert G == literal_graph(I, C)
                count['safe_hierarchy_promotions'] += 1
            suffix = finish_on_graph(I, G)
            assert suffix is not None
            v = (refs[-1].word + suffix[0])[::-1]
            assert witness(I, v) and border_witness(I, v)
            # Check independent earlier finite layer interface on SAME reference.
            old = layer_graph(I, refs[-1], max_states=None, allow_return_completion=False)
            assert old['status'] == 'FOUND_WITNESS'
            count['fixed_finish_graph_oracles'] += 1
    # Witnesses requiring more than two levels: explicitly test every promotion
    # and the endpoint query, without saying the general existential search ran.
    rank_rows = []
    for r in range(2, 8):
        F = make_family((1,) * r); I = F.instance
        w = '10' * r
        run = I.run(w); labels = tuple(reversed(run)); rho = w[::-1]
        depths, milestones = ranks_and_milestones(rho)
        assert max(depths) == r
        refs = [Reference(rho[:j], labels[:j + 1]) for j in milestones]
        for B, C in zip(refs, refs[1:]):
            G, _ = local_extension(I, B, C)
            assert G == literal_graph(I, C)
            count['higher_rank_fixture_promotions'] += 1
        final = finish_on_graph(I, graph_from_reference(I, refs[-1]))
        assert final is not None and witness(I, (refs[-1].word + final[0])[::-1])
        rank_rows.append({'states': len(I.delta), 'word': w, 'rank': r,
                          'milestone_lengths': list(milestones)})
    # Full-return end handling on unary terminal paths.
    for n in range(1, 10):
        I = Instance(tuple((j + 1, -1) for j in range(n)) + ((-1, -1),), frozenset({n}))
        w = '0' * n; run = I.run(w)
        rho = w; labels = tuple(reversed(run))
        for m in range(1, n + 1):
            B = Reference(rho[:m], labels[:m + 1])
            result = finish_on_graph(I, graph_from_reference(I, B))
            assert (result is not None) == (m == n)
            count['full_return_rank_boundary_cases'] += 1
    return {'status': 'PASS', 'seed': SEED,
            'repository_base': '47adf83c194aa941b525240f6470f3d77a69f81d',
            'counts': dict(sorted(count.items())),
            'higher_rank_positive_fixtures': rank_rows,
            'endpoint_wrap_regressions': endpoint_rows,
            'converse_boundary': converse_rows,
            'shared_strip_observers': {'individually_satisfiable': individual, 'jointly_satisfiable': joint},
            'scope': 'Graph identities and finite query-kernel audits only; NOT an executed unrestricted decider',
            'full_query_elimination_compiler_executed': False,
            'independent_mathematical_review': False,
            'lean_checked': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'results/rank-query-graphs.json')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled')
    out = check()
    text = json.dumps(out, indent=2, sort_keys=True) + '\n'
    args.output.write_text(text, encoding='utf-8')
    print(text)

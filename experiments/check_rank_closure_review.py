"""Separate review of rank-query closure; fixed-base all-length oracle checks.

This reviews the candidate at the pinned revision. It does not independently
re-certify C029/C031, constitute Lean verification, or decide new unrestricted
instances by treating resource exhaustion as NO. Python 3.10+, standard library.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import replace
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import random

from border_lab import Instance, words, witness, border_witness
from rank_query_prefix import Reference, ranks_and_milestones, valid_reverse_prefix
from rank_query_graphs import literal_graph, local_extension, first_return
from rank_preimage import (Atom, Query, Model, Budget, Test, TRUE, Map, Observer,
                           fld, table, one_edge, model, path, compile_diagram,
                           extract_diagram, preimages, finish_queries, reconstruct_reference,
                           verify_assignment, InvalidDiagram, END, FIRST, LAST)
from rank_frontier_oracle import fixed_reference_query, explicit_query_truth

BASE = '8b3ac145c67a1f7dabcc7173d76e8f14cca7a27a'
SEED = 20260917113
ROOT = Path(__file__).resolve().parents[1]


def exact(labels):
    return table(len(labels)+1, tuple((j, a, j+1) for j, a in enumerate(labels)),
                 final=(len(labels),))


def root_end_query(observers):
    return Query(('root', 'end'), (('root', fld('root', True)), ('end', fld('end', True))),
                 atoms=tuple(Atom(o, 'end', 'root') for o in observers))


def query_at_assignment(G, Q, assignment):
    if not all(t.holds(G.colours[assignment[v]]) for v, t in Q.tests): return None
    if any(assignment[x] != assignment[y] for x, y in Q.equal): return None
    if any(assignment[x] == assignment[y] for x, y in Q.unequal): return None
    paths = tuple(path(G, a.observer, assignment[a.source], assignment[a.target]) for a in Q.atoms)
    return None if any(p is None for p in paths) else Model(assignment, paths)


def diagram_checks(I, B, C, Q, assignment, counts):
    G = literal_graph(I, C)
    M = query_at_assignment(G, Q, assignment)
    assert M is not None
    D = extract_diagram(I, B, C, Q, M)
    P = compile_diagram(I, Q, D)
    sol = model(literal_graph(I, B), P, Budget(2000000))
    assert sol is not None
    rebuilt, bindings = reconstruct_reference(I, B, D, P, sol)
    assert first_return(B.word, rebuilt.word)
    assert verify_assignment(literal_graph(I, rebuilt), Q, bindings)
    assert explicit_query_truth(literal_graph(I, rebuilt), Q)
    counts['targeted_compiled_diagrams'] += 1
    return D, P


def core_checks():
    C = Counter(); rng = random.Random(SEED)
    toy = Instance(((0, 0),), frozenset())
    # First-milestone claims tested by direct substring/border definitions.
    for w in words('01', 9):
        if not w: continue
        depths = [0]
        for n in range(1, len(w)+1):
            proper = max((j for j in range(n) if w[:n].endswith(w[:j])), default=0)
            depths.append(1+depths[proper])
        ms = tuple(next(i for i, d in enumerate(depths) if d == rank)
                   for rank in range(1, max(depths)+1))
        assert ranks_and_milestones(w) == (tuple(depths), ms)
        for m, n in zip(ms, ms[1:]):
            assert w.find(w[:m], 1)+m == n
            C['literal_milestone_returns'] += 1
        C['literal_rank_words'] += 1
    # Differential finite-query semantics, including failures, aliases and tests.
    for _ in range(280):
        w = rng.choice(tuple(x for x in words('01', 5) if x))
        G = literal_graph(toy, Reference(w, (0,)*(len(w)+1)))
        names = ('x', 'y', 'z'); tests = []
        for name in names:
            if rng.random() < .65:
                f = rng.choice(('root', 'end', 'next_bit'))
                value = rng.choice((True, False)) if f != 'next_bit' else rng.choice(('0', '1', ''))
                tests.append((name, fld(f, value)))
        atoms = []
        for _ in range(rng.randrange(1, 4)):
            size = rng.randrange(1, 4)
            es = [(p, a, q) for p in range(size) for q in range(size)
                  for a in ('F', 'S', 'K0', 'K1') if rng.random() < .22]
            obs = table(size, es, final=(rng.randrange(size),))
            atoms.append(Atom(obs, rng.choice(names), rng.choice(names)))
        equal = (('x', 'y'),) if rng.random() < .15 else ()
        unequal = (('x', 'z'),) if rng.random() < .25 else ()
        Q = Query(names, tuple(tests), equal, unequal, tuple(atoms))
        a = model(G, Q, Budget(300000)) is not None
        b = explicit_query_truth(G, Q)
        assert a == b
        C['independent_finite_query_truths'] += 1
        C['finite_query_yes' if b else 'finite_query_no'] += 1
    # Same old origin, DISTINCT fresh positions. Both F exits go to root.
    B = Reference('0', (0, 0)); V = Reference('0110', (0,)*5)
    Q = Query(('r', 'u', 'v', 'e'), (('r', fld('root', True)), ('e', fld('end', True))),
              unequal=(('u', 'v'),), atoms=(
                  Atom(exact(('S', 'S')), 'r', 'u'),
                  Atom(exact(('S', 'S', 'S')), 'r', 'v'),
                  Atom(one_edge('F'), 'u', 'r'), Atom(one_edge('F'), 'v', 'r'),
                  Atom(one_edge('K0'), 'v', 'e')))
    D, P = diagram_checks(toy, B, V, Q, {'r': 0, 'u': 2, 'v': 3, 'e': 4}, C)
    truth = fixed_reference_query(toy, B, Q, max_states=3000, require_terminal=False)
    assert truth['status'] == 'YES'
    C['distinct_positions_shared_origin'] += 1
    # A singleton fresh strip is simultaneously FIRST and LAST; K0 wraps to itself.
    B2 = Reference('00', (0,)*3); V2 = Reference('000', (0,)*4)
    Q2 = Query(('e',), (('e', fld('end', True)),), atoms=(Atom(one_edge('K0'), 'e', 'e'),))
    D2, _ = diagram_checks(toy, B2, V2, Q2, {'e': 3}, C)
    assert len(D2.groups) == 1
    C['singleton_overlap_wrap'] += 1
    # Explicit coincident fresh variables and zero-length forward query pieces.
    Q3 = Query(('u', 'v'), (('u', fld('end', True)),), equal=(('u', 'v'),),
               atoms=(Atom(table(1, ()), 'u', 'v'),))
    diagram_checks(toy, B2, V2, Q3, {'u': 3, 'v': 3}, C)
    C['coincident_fresh_and_empty_path'] += 1
    # All-length inconsistent shared requirements: length two AND length three.
    def length_query(ns):
        return Query(('r', 'e'), (('r', fld('root', True)), ('e', fld('end', True))),
                     atoms=tuple(Atom(exact(('S',)*n), 'r', 'e') for n in ns))
    shared = []
    for lengths in ((2,), (3,), (2, 3)):
        ans = fixed_reference_query(toy, Reference('0', (0, 0)), length_query(lengths),
                                    max_states=5000, require_terminal=False)
        assert ans['status'] == ('NO' if len(lengths) == 2 else 'YES')
        shared.append({'lengths': list(lengths), **ans})
        C['shared_reference_all_length_queries'] += 1
    # One abstract observer can observe the same physical interval more than once.
    # Compile several real paths with portal exits/wraps and finite-colour tests.
    for text in ('00', '010', '0110', '01110', '000', '01010'):
        baseword = '00' if text == '000' else '010' if text == '01010' else '0'
        base = Reference(baseword, (0,)*(len(baseword)+1))
        ext = Reference(text, (0,)*(len(text)+1))
        assert first_return(baseword, text)
        graph = literal_graph(toy, ext)
        for label in ('F', 'K0', 'K1'):
            obs = table(2, [(0, label, 1), (1, 'S', 1), (1, 'K0', 1), (1, 'K1', 1)], final=(1,))
            q = Query(('e', 'z'), (('e', fld('end', True)),), atoms=(Atom(obs, 'e', 'z'),))
            solution = model(graph, q, Budget(100000))
            if solution is None: continue
            diagram_checks(toy, base, ext, q, solution.assignment, C)
    # Finite terminal reverse-path families supply COMPLETE extension oracles.
    terminals = []
    for n in range(2, 6):
        delta = tuple((i+1, -1) for i in range(n))+((-1, -1),)
        for mask in range(8):
            flags = frozenset(((0, n-1), (1, n-1), (0, 1))[j] for j in range(3) if mask >> j & 1)
            I = Instance(delta, frozenset({n}), flags)
            for m in range(1, n):
                b = Reference('0'*m, tuple(range(n, n-m-1, -1)))
                if not valid_reverse_prefix(I, b.word, b.labels): continue
                # With unary input, the sole first return extends by ONE letter.
                v = Reference('0'*(m+1), tuple(range(n, n-m-2, -1)))
                for target in range(n+1):
                    q = Query(('e',), (('e', fld('end', True)), ('e', fld('state', target))),
                              atoms=(Atom(table(1, [(0, 'F', 0)]), 'e', 'e'),))
                    expected = valid_reverse_prefix(I, v.word, v.labels) and explicit_query_truth(literal_graph(I, v), q)
                    ans = fixed_reference_query(I, b, q, max_states=10000)
                    assert ans['status'] == ('YES' if expected else 'NO')
                    C['complete_terminal_extension_queries'] += 1
                    C['terminal_extension_yes' if expected else 'terminal_extension_no'] += 1
    # Re-apply ACTUAL compiled output on non-unary, coloured terminal paths.
    # These are selected positive branches, not exhaustive high-rank unions.
    nested = []
    for rho in ('0110110110', '0100101010', '0010110010110'):
        w = rho[::-1]; n = len(w)
        delta = tuple(tuple(i+1 if w[i] == a else -1 for a in '01') for i in range(n))+((-1,-1),)
        agreements = {(i,j) for i in range(n+1) for j in range(i,n+1) if w[i:].startswith(w[j:])}
        flags = frozenset((p,q) for p in range(n+1) for q in range(n+1)
                          if (p,q) not in agreements and (11*p+7*q)%5 == 0)
        I = Instance(delta, frozenset({n}), flags)
        assert witness(I,w) and border_witness(I,w)
        labels = tuple(range(n,-1,-1)); ms = ranks_and_milestones(rho)[1]
        refs = [Reference(rho[:m],labels[:m+1]) for m in ms]
        query = next(q for q in finish_queries(I)
                     if model(literal_graph(I,refs[-1]),q,Budget(500000)))
        weights = [query.weight]
        for b,v in reversed(list(zip(refs,refs[1:]))):
            actual = model(literal_graph(I,v),query,Budget(2000000)); assert actual
            diagram = extract_diagram(I,b,v,query,actual)
            previous = compile_diagram(I,query,diagram)
            solved = model(literal_graph(I,b),previous,Budget(2000000)); assert solved
            rebuilt,assignment = reconstruct_reference(I,b,diagram,previous,solved)
            assert verify_assignment(literal_graph(I,rebuilt),query,assignment,Budget(2000000))
            assert valid_reverse_prefix(I,rebuilt.word,rebuilt.labels)
            query = previous; weights.append(query.weight)
            C['successive_coloured_preimages'] += 1
        assert len(refs[0].word) == 1
        nested.append(dict(reverse_word=rho,word=w,states=n+1,flags=len(flags),
                           milestones=list(ms),clause_weights=weights))
    assert fixed_reference_query(toy, Reference('0',(0,0)), root_end_query((table(1, [(0,'S',0)]),)),
                                 max_states=1, require_terminal=False)['status'] == 'UNKNOWN'
    C['frontier_cap_regressions'] += 1
    return {'counts': dict(sorted(C.items())), 'shared_word_cases': shared, 'nested_compilation': nested}


def union_checks(start=0, stop=16):
    I = Instance(((0, 0),), frozenset())
    bases = tuple(Reference(w, (0,)*(len(w)+1)) for w in ('0', '1', '00', '01', '10', '11', '010'))
    graphs = tuple(literal_graph(I, B) for B in bases)
    labels = ('F', 'S', 'K0', 'K1')
    counts = Counter(); records = []
    for mask in range(start, stop):
        chosen = tuple(a for j, a in enumerate(labels) if mask >> j & 1)
        Q = root_end_query((table(1, [(0, a, 0) for a in chosen]),))
        answers = [fixed_reference_query(I, B, Q, max_states=10000, require_terminal=False) for B in bases]
        assert all(a['status'] in ('YES', 'NO') for a in answers)
        budget = Budget(5000000); hits = [0]*len(bases); clauses = 0; evaluations = 0
        for P in preimages(I, Q, budget):
            clauses += 1
            for j, G in enumerate(graphs):
                # Existence is settled by one model. Negative bases still test
                # EVERY emitted clause; the syntactic union is fully enumerated.
                if hits[j]: continue
                evaluations += 1
                sat = model(G, P, budget) is not None
                if sat:
                    hits[j] = clauses
                    assert answers[j]['status'] == 'YES'
        assert [bool(h) for h in hits] == [a['status']=='YES' for a in answers]
        counts['complete_syntactic_unions'] += 1
        counts['fully_enumerated_clauses'] += clauses
        counts['clause_base_evaluations'] += evaluations
        counts['complete_all_length_oracle_comparisons'] += len(bases)
        counts['all_length_yes'] += sum(a['status']=='YES' for a in answers)
        counts['all_length_no'] += sum(a['status']=='NO' for a in answers)
        records.append(dict(labels=list(chosen), clauses=clauses, work=budget.used,
                            bases=[dict(base=B.word, first_satisfying_clause=h, **ans) for B, h, ans in zip(bases, hits, answers)]))
    return {'counts': dict(sorted(counts.items())), 'full_unions': records}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def compact(result):
    """Retain every verdict; full matrices/models regenerate with --full-output."""
    out = dict(result)
    if 'unions' in out:
        out['unions'] = dict(result['unions'])
        out['unions']['full_unions'] = [
            dict(labels=r['labels'], clauses=r['clauses'], work=r['work'],
                 base_order=[b['base'] for b in r['bases']],
                 verdicts=[b['status'] for b in r['bases']],
                 frontier_states=[b['states'] for b in r['bases']],
                 first_satisfying_clauses=[b['first_satisfying_clause'] for b in r['bases']])
            for r in result['unions']['full_unions']]
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, default=ROOT/'results/rank-closure-review.json')
    p.add_argument('--full-output', type=Path)
    p.add_argument('--part', choices=('core', 'unions', 'all'), default='all')
    p.add_argument('--mask-start', type=int, default=0)
    p.add_argument('--mask-stop', type=int, default=16)
    args = p.parse_args()
    if not 0 <= args.mask_start <= args.mask_stop <= 16: p.error('Mask range must lie in 0..16')
    if not __debug__: p.error('Assertions must be enabled')
    result = dict(status='PASS', reviewed_commit=BASE, seed=SEED, part=args.part)
    if args.part in ('core','all'): result['core'] = core_checks()
    if args.part in ('unions','all'): result['unions'] = union_checks(args.mask_start, args.mask_stop)
    result['reviewed_blobs'] = {f:git_blob(ROOT/'experiments'/f) for f in
                              ('rank_preimage.py', 'rank_preimage_core.py', 'rank_query_graphs.py',
                               'rank_query_prefix.py', 'border_lab.py')}
    result['limits'] = ['The frontier oracle fixes B; it is not a uniform preimage theorem.',
                        'The full unions here have one path atom; joint tests use the independent fixed-base oracle and selected compiled diagrams.',
                        'Finite regression evidence does not certify the all-query mathematical statement.',
                        'No fresh independent review of C029/C031 or Lean verification is claimed.']
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(compact(result), indent=2, sort_keys=True)+'\n')
    if args.full_output:
        args.full_output.parent.mkdir(parents=True, exist_ok=True)
        args.full_output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('core','unions')}, indent=2, sort_keys=True))
    for part in ('core','unions'):
        if part in result: print(part, result[part]['counts'])


if __name__ == '__main__': main()

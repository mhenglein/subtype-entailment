#!/usr/bin/env python3
"""Differential check of the Lean diagram compiler against `rank_preimage.compile_diagram`.

`lean/Subtail/RankQueryCompiler.lean` defines an executable `compileDiagram`
that turns one bounded portal diagram into one clause of the pinned query
grammar.  This script builds certificate diagrams exactly as the fixture
checker does (brute-force extension `C` of a base `B`, `extract_diagram`),
translates instance, clause and diagram to Lean literals, and compares, for
several base references `B'`:

    Python: compile_diagram raises            <->  Lean: compileDiagram = none
    Python: model(P(B'), compile_diagram(D))  <->  Lean: satCheck (prefixGraph I B') [P]

Mutated diagrams (wrong first bit, wrong first state, shifted controls) are
included so that rejections are compared too.  Finite agreement is regression
evidence for the TRANSLATION of the compiler; it proves nothing about the
Closure Lemma.  Without `--lean` only the Python side runs.  Standard library
only; Lean 4.33.1 through `lake env lean`.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import random
from collections import Counter
from dataclasses import replace
from pathlib import Path

from border_lab import Instance
from check_closure_fixtures import exact, extensions, is_terminal, loop, truth
from check_lean_rank_query import (LEAN_LABEL, PRELUDE, fin, lean_clause, lean_instance,
                                   lean_reference, random_terminal, run_lean, safe_references)
from rank_preimage import END, FIRST, LAST, Budget, InvalidDiagram, compile_diagram, extract_diagram
from rank_preimage_core import Atom, Query, fld, model, one_edge, table
from rank_query_graphs import literal_graph
from rank_query_prefix import Reference

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026091841

COMPILER_PRELUDE = PRELUDE.replace('import Subtail.RankQuery\nopen Subtail RankQuery',
                                   'import Subtail.RankQueryCompiler\nopen Subtail RankQuery RankQueryCompiler') + '''
def leanNext : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def report {k : Nat} (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k) : String :=
  match compileDiagram I c D with
  | none => "INVALID"
  | some P => toString (satCheck (prefixGraph I B) [P])
'''


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


# ----------------------------------------------------------------------------
# Lean literal emission for observers and diagrams
# ----------------------------------------------------------------------------

def lean_observer_any(o, k: int) -> str:
    if o.kind == 'table':
        from check_lean_rank_query import lean_observer
        return lean_observer(o, k)
    if o.kind == 'edge':
        label, left, right, semantic = o.data
        assert semantic is None and left.kind == 'true' and right.kind == 'true', o
        return f'(oneEdge {LEAN_LABEL[label]} : Observer {k})'
    raise ValueError('Unsupported observer kind for translation: ' + o.kind)


def lean_clause_any(Q: Query, k: int) -> str:
    index = {v: i for i, v in enumerate(Q.variables)}
    from check_lean_rank_query import lean_test
    tests = ', '.join(f'({fin(index[v])}, fun c => {lean_test(t, k)})' for v, t in Q.tests)
    equal = ', '.join(f'({fin(index[x])}, {fin(index[y])})' for x, y in Q.equal)
    unequal = ', '.join(f'({fin(index[x])}, {fin(index[y])})' for x, y in Q.unequal)
    atoms = ', '.join(f'⟨{lean_observer_any(a.observer, k)}, {fin(index[a.source])}, {fin(index[a.target])}⟩'
                      for a in Q.atoms)
    return (f'{{ vars := {len(Q.variables)}, tests := [{tests}], equal := [{equal}], '
            f'unequal := [{unequal}], atoms := ([{atoms}] : List (Atom {k} {len(Q.variables)})) }}')


def lean_colour(c, k: int) -> str:
    nxt = {'0': 'some false', '1': 'some true', '': 'none'}[c.next_bit]
    mask = ', '.join('true' if c.forbidden >> p & 1 else 'false' for p in range(k))
    return (f'⟨{fin(c.state)}, #v[{mask}], ({nxt} : Option Bool), '
            f'{"true" if c.root else "false"}, {"true" if c.end else "false"}⟩')


def core_names(D) -> list[str]:
    names = {name for _, kind, name in D.locations if kind == 'core'}
    for pieces in D.pieces:
        for P in pieces:
            if P.kind in ('core', 'enter'):
                names.add(P.source)
            if P.kind in ('core', 'exit'):
                names.add(P.target)
    return sorted(names)


def lean_diagram(D, Q: Query, k: int) -> str:
    group = {name: i for i, names in enumerate(D.groups) for name in names}
    cores = {name: i for i, name in enumerate(core_names(D))}
    loc = {v: (kind, name) for v, kind, name in D.locations}
    locs = []
    for v in Q.variables:
        kind, name = loc[v]
        locs.append(f'.core {cores[name]}' if kind == 'core' else f'.fresh {group[name]}')
    def piece(P):
        if P.kind == 'core':
            s, t = cores[P.source], cores[P.target]
        elif P.kind == 'forward' or P.kind == 'wrap':
            s, t = group[P.source], group[P.target]
        elif P.kind == 'enter':
            s, t = cores[P.source], group[P.target]
        else:
            s, t = group[P.source], cores[P.target]
        label = LEAN_LABEL[P.label] if P.label else '.F'
        return (f'{{ kind := .{P.kind}, source := {s}, target := {t}, lc := {P.left_control}, '
                f'rc := {P.right_control}, label := {label} }}')
    pieces = ', '.join('[' + ', '.join(piece(P) for P in ps) + ']' for ps in D.pieces)
    states = ', '.join(fin(q) for q in D.states)
    nexts = ', '.join({'0': 'some false', '1': 'some true', '': 'none'}[b] for b in D.next_bits)
    seams = ', '.join(f'({a}, {b}, {g}, {c})' for a, b, g, c in D.intermediate_controls)
    return (f'{{ groups := {len(D.groups)}, coreVars := {len(cores)}, loc := [{", ".join(locs)}], '
            f'states := ([{states}] : List (Fin {k})), nextBits := ([{nexts}] : List (Option Bool)), '
            f'firstBit := {"true" if D.first_bit == "1" else "false"}, oldEnd := {lean_colour(D.old_end_colour, k)}, '
            f'pieces := [{pieces}], seams := [{seams}] }}')


# ----------------------------------------------------------------------------
# Python side
# ----------------------------------------------------------------------------

def python_report(I, Q, D, B) -> str:
    try:
        P = compile_diagram(I, Q, D)
    except (InvalidDiagram, KeyError):
        return 'INVALID'
    return 'true' if model(literal_graph(I, B), P, Budget(3000000)) is not None else 'false'


def mutations(D, k: int, rng: random.Random):
    """Diagram variants that may or may not compile; both sides must agree."""
    yield 'first_bit', replace(D, first_bit='1' if D.first_bit == '0' else '0')
    if k > 1:
        states = list(D.states)
        states[0] = (states[0] + 1) % k
        yield 'first_state', replace(D, states=tuple(states))
    if D.pieces and D.pieces[0]:
        P = D.pieces[0][0]
        shifted = replace(P, right_control=P.right_control + 1)
        yield 'control', replace(D, pieces=(((shifted,) + tuple(D.pieces[0][1:])),) + tuple(D.pieces[1:]))
    if len(D.groups) > 1:
        bits = list(D.next_bits)
        bits[0] = '1' if bits[0] == '0' else '0'
        yield 'next_bit', replace(D, next_bits=tuple(bits))


def fixture_queries(k: int):
    root_end = lambda obs: Query(('r', 'e'), (('r', fld('root', True)), ('e', fld('end', True))),
                                 atoms=tuple(Atom(o, 'e', 'r') for o in obs))
    yield 'S2 root->end', Query(('r', 'e'), (('r', fld('root', True)), ('e', fld('end', True))),
                                atoms=(Atom(exact(('S', 'S')), 'r', 'e'),))
    yield 'K1 end->root', root_end((exact(('K1',)),))
    yield 'loop F,S,K1', root_end((loop(('F', 'S', 'K1')),))
    yield 'two atoms K1 | F,S', Query(('r', 'e'), (('r', fld('root', True)), ('e', fld('end', True))),
                                      atoms=(Atom(exact(('K1',)), 'e', 'r'), Atom(loop(('F', 'S')), 'e', 'r')))
    yield 'F edge then S', Query(('e', 'u', 'r'), (('e', fld('end', True)), ('r', fld('root', True))),
                                 atoms=(Atom(one_edge('F'), 'e', 'u'), Atom(exact(('S',)), 'u', 'r')))
    yield 'K0 self wrap', Query(('e',), (('e', fld('end', True)),), atoms=(Atom(one_edge('K0'), 'e', 'e'),))
    yield 'zero-length shared', Query(('e', 'u'), (('e', fld('end', True)),), equal=(('e', 'u'),),
                                      atoms=(Atom(table(1, ()), 'e', 'u'), Atom(loop(('F',)), 'e', 'u')))


def build(rng: random.Random, quick: bool):
    toy = Instance(((0, 0),), frozenset())
    instances = [('toy', toy, [Reference('0', (0, 0)), Reference('00', (0, 0, 0)), Reference('01', (0, 0, 0))])]
    for k in (2, 3):
        I = random_terminal(rng, k)
        refs = safe_references(I, 5)
        rng.shuffle(refs)
        instances.append((f'k{k}', I, refs[:3]))
    src = [COMPILER_PRELUDE]
    expectations = []
    counts = Counter()
    records = []
    for n, (tag, I, bases) in enumerate(instances):
        k = len(I.delta)
        src.append(lean_instance(f'I{n}', I))
        other_refs = safe_references(I, 4) if tag != 'toy' else [Reference('1', (0, 0)), Reference('10', (0, 0, 0))]
        for r, B in enumerate(bases + other_refs):
            src.append(lean_reference(f'B{n}_{r}', k, B))
        all_bases = bases + other_refs
        for qi, (qname, Q) in enumerate(fixture_queries(k)):
            if tag != 'toy' and qname in ('K0 self wrap', 'zero-length shared'):
                continue
            src.append(f'def Q{n}_{qi} : Clause {k} := {lean_clause_any(Q, k)}')
            for bi, B in enumerate(bases):
                terminal = is_terminal(I) and B.labels[0] in I.final
                found = [C for C in extensions(I, B, 4 if tag == 'toy' else 3, terminal)
                         if truth(literal_graph(I, C), Q)]
                counts['brute_force_extensions'] += len(found)
                for ci, C in enumerate(found[:2 if quick else 4]):
                    sol = model(literal_graph(I, C), Q, Budget(2000000))
                    assert sol is not None, (tag, qname, C.word)
                    D = extract_diagram(I, B, C, Q, sol)
                    variants = [('certificate', D)] + list(mutations(D, k, rng))
                    for vname, DV in variants:
                        dname = f'D{n}_{qi}_{bi}_{ci}_{vname}'
                        src.append(f'def {dname} : Diagram {k} := {lean_diagram(DV, Q, k)}')
                        for ri, B2 in enumerate(all_bases):
                            expected = python_report(I, Q, DV, B2)
                            if vname == 'certificate' and ri == bi:
                                assert expected == 'true', (tag, qname, C.word)
                            src.append(f'#eval IO.println s!"@{{report I{n} Q{n}_{qi} {dname} B{n}_{ri}}}"')
                            expectations.append(expected)
                            counts['comparisons'] += 1
                            counts['expected_' + expected] += 1
                        counts['diagrams'] += 1
                        counts['variant_' + vname] += 1
                    records.append(dict(instance=tag, query=qname, base=B.word, extension=C.word,
                                        groups=len(D.groups), atoms=len(Q.atoms)))
    return '\n'.join(src), expectations, dict(sorted(counts.items())), records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='evaluate natively in Lean')
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT / 'results/lean-rank-compiler.json')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled')
    rng = random.Random(SEED)
    source, expectations, counts, records = build(rng, args.quick)
    result = dict(status='PASS', seed=SEED, quick=args.quick, counts=counts, eval_lines=len(expectations),
                  lean_source_blob=git_blob(ROOT / 'lean/Subtail/RankQueryCompiler.lean'),
                  compiler_blob=git_blob(ROOT / 'experiments/rank_preimage.py'),
                  native_lean='NOT_RUN', diagrams=records,
                  limits=['Finite translation regression; nothing about the Closure Lemma is proved.',
                          'Only table and plain one-edge observers are translated.'])
    if args.lean:
        actual = run_lean(source)
        if len(actual) != len(expectations):
            raise SystemExit(f'Lean produced {len(actual)} lines, expected {len(expectations)}')
        mismatches = [(i, a, e) for i, (a, e) in enumerate(zip(actual, expectations)) if a != e]
        result['native_lean'] = 'PASS' if not mismatches else 'FAIL'
        result['mismatches'] = mismatches[:20]
        if mismatches:
            result['status'] = 'FAIL'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'diagrams'}, indent=2, sort_keys=True))
    if result['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Differential check of the Lean rank-query semantics against the Python compiler core.

`lean/Subtail/RankQuery.lean` pins the query grammar, the literal prefix graph and
an executable, kernel-checked-correct decision `satCheck` of query satisfaction.
This script translates small Python fixtures (instances, safe references, table
observers, clauses) into Lean literals, evaluates them natively with the pinned
toolchain, and compares:

* the literal prefix graph `prefixGraph I B` (colours and F/S/K0/K1 edges) with
  `rank_query_graphs.literal_graph`;
* `satCheck (prefixGraph I B) φ` with `rank_preimage_core.model` and with the
  separate `rank_frontier_oracle.explicit_query_truth`;
* `satCheck (prefixGraph I B) (finishQuery I)` with `rank_preimage.finish_queries`.

Finite agreement is regression evidence for the TRANSLATION and the semantics;
it is not the proof of any all-length statement and it does not touch the Closure
Lemma itself.  Without `--lean` only the Python-side fixtures are generated and
cross-checked.  Standard library only; Lean 4.33.1 through `lake env lean`.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import json
import random
import subprocess
from collections import Counter
from pathlib import Path

from border_lab import Instance, witness, words
from rank_frontier_oracle import explicit_query_truth
from rank_preimage import finish_queries
from rank_preimage_core import Atom, Budget, Query, Test, fld, model, table
from rank_query_graphs import literal_graph
from rank_query_prefix import Reference, valid_reverse_prefix

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026091801
LABELS = ('F', 'S', 'K0', 'K1')
LEAN_LABEL = {'F': '.F', 'S': '.S', 'K0': '(.K false)', 'K1': '(.K true)'}


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


# ----------------------------------------------------------------------------
# Lean literal emission
# ----------------------------------------------------------------------------

def fin(i: int) -> str:
    return f'⟨{i}, by decide⟩'


def bools(bits) -> str:
    return '#v[' + ', '.join('true' if b else 'false' for b in bits) + ']'


def lean_instance(name: str, I: Instance) -> str:
    k = len(I.delta)
    rows = []
    for row in I.delta:
        cells = ['none' if t < 0 else f'some {fin(t)}' for t in row]
        rows.append(f'({cells[0]}, {cells[1]})')
    flags = ', '.join(bools((p, q) in I.flags for q in range(k)) for p in range(k))
    return (f'def {name} : Instance {k} where\n'
            f'  initial := {fin(I.start)}\n'
            f'  transitions := #v[{", ".join(rows)}]\n'
            f'  bad := {bools(q in I.bad for q in range(k))}\n'
            f'  final := {bools(q in I.final for q in range(k))}\n'
            f'  flags := #v[{flags}]\n')


def lean_word(word: str) -> str:
    return '[' + ', '.join('true' if a == '1' else 'false' for a in word) + ']'


def lean_reference(name: str, k: int, B: Reference) -> str:
    labels = '[' + ', '.join(fin(q) for q in B.labels) + ']'
    return (f'def {name} : Reference {k} := ⟨{lean_word(B.word)}, '
            f'fun j => ({labels} : List (Fin {k})).getD j {fin(0)}⟩\n')


def lean_test(t: Test, k: int) -> str:
    kind, a = t.kind, t.args
    if kind == 'true':
        return 'true'
    if kind == 'false':
        return 'false'
    if kind == 'field':
        field, value = a
        if field == 'root':
            return f'(c.root == {"true" if value else "false"})'
        if field == 'end':
            return f'(c.isEnd == {"true" if value else "false"})'
        if field == 'next_bit':
            lit = {'0': 'some false', '1': 'some true', '': 'none'}[value]
            return f'(c.next == ({lit} : Option Bool))'
        if field == 'state':
            return f'(c.state.val == {value})'
        if field == 'forbidden':
            return f'(c.mask.toList == [{", ".join("true" if value >> p & 1 else "false" for p in range(k))}])'
        raise ValueError(field)
    if kind == 'clear':
        field, bit = a
        assert field == 'forbidden'
        return f'(!c.mask.get {fin(bit)})'
    if kind == 'and':
        return '(' + ' && '.join(lean_test(x, k) for x in a) + ')'
    if kind == 'not':
        return f'(!{lean_test(a[0], k)})'
    raise ValueError('Unsupported test kind for translation: ' + kind)


def lean_observer(o, k: int) -> str:
    """Translate a `table` observer: colour-independent moves, per-control tests."""
    assert o.kind == 'table', o.kind
    predicates, edges = o.data
    allow = ' '.join(f'| {q} => {lean_test(predicates[q], k)}' for q in range(o.size))
    moves = ', '.join(f'({q}, {LEAN_LABEL[l]}, {p})' for q, l, p in edges) or ''
    return (f'(obsTable {k} {o.size} [{", ".join(map(str, o.initial))}] '
            f'[{", ".join(map(str, sorted(o.final)))}] [{moves}] '
            f'(fun q c => match q with {allow} | _ => true))')


def lean_clause(Q: Query, k: int) -> str:
    index = {v: i for i, v in enumerate(Q.variables)}
    tests = ', '.join(f'({fin(index[v])}, fun c => {lean_test(t, k)})' for v, t in Q.tests)
    equal = ', '.join(f'({fin(index[x])}, {fin(index[y])})' for x, y in Q.equal)
    unequal = ', '.join(f'({fin(index[x])}, {fin(index[y])})' for x, y in Q.unequal)
    atoms = ', '.join(f'⟨{lean_observer(a.observer, k)}, {fin(index[a.source])}, {fin(index[a.target])}⟩'
                      for a in Q.atoms)
    return (f'{{ vars := {len(Q.variables)}, tests := [{tests}], equal := [{equal}], '
            f'unequal := [{unequal}], atoms := ([{atoms}] : List (Atom {k} {len(Q.variables)})) }}')


PRELUDE = '''import Subtail.RankQuery
open Subtail RankQuery

def obsTable (k n : Nat) (ini fin : List Nat) (moves : List (Nat × Label × Nat))
    (allow : Nat → Colour k → Bool) : Observer k where
  size := n
  initial := (List.finRange n).filter fun q => q.val ∈ ini
  final := (List.finRange n).filter fun q => q.val ∈ fin
  allows := fun q c => allow q.val c
  move := fun q _ l _ => (List.finRange n).filter fun p => (q.val, l, p.val) ∈ moves

def row {k : Nat} (G : Graph k) (j : Fin G.size) : List Nat :=
  let c := G.colour j
  let enc : Option (Fin G.size) → Nat := fun o => match o with | none => 1000 | some v => v.val
  let nx : Nat := match c.next with | none => 2 | some false => 0 | some true => 1
  [j.val, c.state.val] ++ c.mask.toList.map (fun b => if b then 1 else 0) ++
    [nx, if c.root then 1 else 0, if c.isEnd then 1 else 0,
     enc (G.edge j .F), enc (G.edge j .S), enc (G.edge j (.K false)), enc (G.edge j (.K true))]

def readback {k : Nat} (G : Graph k) : List (List Nat) :=
  (List.finRange G.size).map (row G)
'''


def python_rows(I: Instance, B: Reference) -> list[list[int]]:
    G = literal_graph(I, B)
    k = len(I.delta)
    edge = {(u, a): v for u, a, v in G.edges}
    out = []
    for j, c in enumerate(G.colours):
        nx = {'0': 0, '1': 1, '': 2}[c.next_bit]
        out.append([j, c.state] + [c.forbidden >> p & 1 for p in range(k)] +
                   [nx, int(c.root), int(c.end), edge[j, 'F'], edge.get((j, 'S'), 1000),
                    edge[j, 'K0'], edge[j, 'K1']])
    return out


# ----------------------------------------------------------------------------
# Fixture generation
# ----------------------------------------------------------------------------

def random_terminal(rng: random.Random, k: int) -> Instance:
    while True:
        delta = tuple(tuple(rng.randrange(-1, k) for _ in '01') for _ in range(k - 1)) + ((-1, -1),)
        flags = frozenset((p, q) for p in range(k) for q in range(k) if rng.random() < 0.2)
        bad = frozenset(q for q in range(k - 1) if rng.random() < 0.1)
        I = Instance(delta, frozenset({k - 1}), flags, bad, start=rng.randrange(k))
        refs = safe_references(I, 6)
        if refs:
            return I


def safe_references(I: Instance, max_len: int) -> list[Reference]:
    """Reversed prefixes of actual witnesses; every one is a safe labelled reference."""
    refs, seen = [], set()
    for w in words('01', max_len):
        if not w or not witness(I, w):
            continue
        rho, labels = w[::-1], I.run(w)[::-1]
        for m in range(1, len(rho) + 1):
            B = Reference(rho[:m], labels[:m + 1])
            if B in seen:
                continue
            assert valid_reverse_prefix(I, B.word, B.labels)
            seen.add(B)
            refs.append(B)
    return refs


def random_test(rng: random.Random, k: int, colours) -> Test:
    c = rng.choice(colours)
    kind = rng.choice(('root', 'end', 'next_bit', 'state', 'forbidden', 'clear', 'and', 'not'))
    if kind in ('root', 'end', 'next_bit', 'state', 'forbidden'):
        return fld(kind, getattr(c, kind))
    if kind == 'clear':
        return Test('clear', ('forbidden', rng.randrange(k)))
    if kind == 'and':
        return Test('and', (fld('root', c.root), fld('end', rng.choice((True, False)))))
    return Test('not', (fld('next_bit', c.next_bit),))


def random_query(rng: random.Random, I: Instance, G, variables=('x', 'y', 'z')) -> Query:
    k = len(I.delta)
    tests = tuple((v, random_test(rng, k, G.colours)) for v in variables if rng.random() < 0.5)
    atoms = []
    for _ in range(rng.randrange(1, 4)):
        size = rng.randrange(1, 4)
        edges = [(p, a, q) for p in range(size) for q in range(size) for a in LABELS if rng.random() < 0.3]
        predicates = tuple(random_test(rng, k, G.colours) if rng.random() < 0.3 else Test() for _ in range(size))
        o = table(size, edges, final=(rng.randrange(size),), predicates=predicates)
        atoms.append(Atom(o, rng.choice(variables), rng.choice(variables)))
    equal = (('x', 'y'),) if rng.random() < 0.15 else ()
    unequal = (('x', 'z'),) if rng.random() < 0.25 else ()
    return Query(variables, tests, equal, unequal, tuple(atoms))


def build_fixtures(rng: random.Random):
    """Return (lean_source, expectations). Expectations are ordered like the #eval lines."""
    toy = Instance(((0, 0),), frozenset())
    instances = [toy] + [random_terminal(rng, k) for k in (2, 3, 3, 3, 2)]
    src = [PRELUDE]
    expectations = []
    counts = Counter()
    for n, I in enumerate(instances):
        k = len(I.delta)
        src.append(lean_instance(f'I{n}', I))
        refs = safe_references(I, 6 if k > 1 else 4)
        rng.shuffle(refs)
        for r, B in enumerate(refs[:12]):
            name = f'B{n}_{r}'
            src.append(lean_reference(name, k, B))
            G = literal_graph(I, B)
            src.append(f'#eval IO.println s!"@{{toString (readback (prefixGraph I{n} {name}))}}"')
            expectations.append(('graph', str(python_rows(I, B))))
            counts['graphs'] += 1
            expected = any(model(G, q, Budget(200000)) is not None for q in finish_queries(I))
            src.append(f'#eval IO.println s!"@{{satCheck (prefixGraph I{n} {name}) (finishQuery I{n})}}"')
            expectations.append(('finish', 'true' if expected else 'false'))
            counts['finish_queries'] += 1
            for _ in range(4):
                clauses = [random_query(rng, I, G) for _ in range(rng.randrange(1, 3))]
                truth = [model(G, Q, Budget(300000)) is not None for Q in clauses]
                oracle = [explicit_query_truth(G, Q) for Q in clauses]
                assert truth == oracle, (I, B, clauses)
                expected = any(truth)
                lean_union = '[' + ', '.join(lean_clause(Q, k) for Q in clauses) + ']'
                src.append(f'#eval IO.println s!"@{{satCheck (prefixGraph I{n} {name}) ({lean_union} : Query {k})}}"')
                expectations.append(('sat', 'true' if expected else 'false'))
                counts['sat_queries'] += 1
                counts['sat_clauses'] += len(clauses)
                counts['sat_yes' if expected else 'sat_no'] += 1
    return '\n'.join(src), expectations, dict(counts)


def run_lean(source: str) -> list[str]:
    lean_dir = ROOT / 'lean'
    version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=lean_dir,
                             capture_output=True, text=True, check=True).stdout.strip()
    if '4.33.1' not in version:
        raise SystemExit('Pinned toolchain Lean 4.33.1 required, found: ' + version)
    scratch = ROOT / 'tmp' / 'lean-rank-query-fixtures.lean'
    scratch.parent.mkdir(exist_ok=True)
    scratch.write_text(source)
    done = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=lean_dir,
                          capture_output=True, text=True)
    if done.returncode != 0:
        raise SystemExit('Lean evaluation failed:\n' + done.stdout + done.stderr)
    return [line.strip()[1:] for line in done.stdout.splitlines() if line.strip().startswith('@')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='evaluate the fixtures natively in Lean')
    parser.add_argument('--output', type=Path, default=ROOT / 'results/lean-rank-query.json')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled')
    rng = random.Random(SEED)
    source, expectations, counts = build_fixtures(rng)
    result = dict(status='PASS', seed=SEED, fixtures=counts, eval_lines=len(expectations),
                  lean_source_blob=git_blob(ROOT / 'lean/Subtail/RankQuery.lean'),
                  native_lean='NOT_RUN',
                  scope='Translation/semantics differential on small fixtures; not a proof of the Closure Lemma')
    if args.lean:
        lines = run_lean(source)
        if len(lines) != len(expectations):
            raise SystemExit(f'Expected {len(expectations)} outputs, got {len(lines)}')
        mismatches = []
        for i, ((kind, expected), got) in enumerate(zip(expectations, lines)):
            if kind == 'graph':
                same = ast.literal_eval(got) == ast.literal_eval(expected)
            else:
                same = got == expected
            if not same:
                mismatches.append(dict(index=i, kind=kind, expected=expected, lean=got))
        result['native_lean'] = dict(status='PASS' if not mismatches else 'FAIL',
                                     toolchain='leanprover/lean4:v4.33.1', mismatches=mismatches)
        if mismatches:
            result['status'] = 'FAIL'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))
    if result['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()

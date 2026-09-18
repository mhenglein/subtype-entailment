#!/usr/bin/env python3
"""Independent finite-syntax census versus executable Lean enumeration (#28).

This tests explicit syntax budgets, NOT semantic extension completeness.
Native Lean is mandatory unless --python-only is explicitly selected.
No solver verdict about unrestricted BorderAvoid is produced.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def lists(xs: list, length: int) -> list[list]:
    return [list(t) for t in itertools.product(xs, repeat=length)]

def upto(xs: list, length: int) -> list[list]:
    return [row for n in range(length + 1) for row in lists(xs, n)]

def colours(k: int) -> list[list[int]]:
    return [[q, *mask, nxt, root, end]
            for q, mask, nxt, root, end in itertools.product(
                range(k), lists([0, 1], k), range(3), range(2), range(2))]

def pieces(n: int) -> list[list[int]]:
    return [list(t) for t in itertools.product(range(5), range(n), range(n),
                                             range(n), range(n), range(4))]

def seams(n: int) -> list[list[int]]:
    return [list(t) for t in itertools.product(range(n), repeat=4)]

def flat(xs: list[list]) -> list:
    return [x for row in xs for x in row]

def census(k: int, v: int, a: int, b: tuple[int, ...]) -> list[list[list[int]]]:
    """Literal cartesian product over independently stated field ranges."""
    groups, core, per_atom, seam_entries, scalar = b
    output = []
    for g in range(1, groups + 1):
        for c in range(core + 1):
            locs = [[0, x] for x in range(c)] + [[1, x] for x in range(g)]
            for loc, qs, nxt, first, old, paths, joins in itertools.product(
                lists(locs, v), lists(list(range(k)), g), lists([0, 1, 2], g),
                range(2), colours(k), lists(upto(pieces(scalar), per_atom), a),
                upto(seams(scalar), seam_entries)
            ):
                output.append([[g, c], flat(loc), qs, nxt, [first], old,
                               [len(ps) for ps in paths], flat(flat(paths)), flat(joins)])
    return output

def formula_count(k: int, v: int, a: int, b: tuple[int, ...]) -> int:
    gmax, cmax, pmax, jmax, n = b
    path_count = sum((20 * n**4)**i for i in range(pmax + 1))**a
    join_count = sum((n**4)**i for i in range(jmax + 1))
    colour_count = k * 2**k * 3 * 2 * 2
    return sum((c + g)**v * k**g * 3**g * 2 * colour_count * path_count * join_count
               for g in range(1, gmax + 1) for c in range(cmax + 1))

# (state alphabet, variables, trivial self-path atoms, five syntax caps)
SHAPES = [
    (0, 0, 0, (1, 0, 0, 0, 0)),
    (1, 0, 0, (0, 0, 0, 0, 0)),
    (1, 0, 0, (1, 0, 0, 0, 0)),
    (1, 1, 0, (1, 0, 0, 0, 0)),
    (1, 1, 0, (1, 1, 0, 0, 0)),
    (1, 1, 0, (2, 0, 0, 0, 0)),
    (2, 0, 0, (1, 0, 0, 0, 0)),
    (2, 1, 0, (1, 0, 0, 0, 0)),
    (1, 1, 1, (1, 0, 1, 0, 1)),
    (1, 1, 1, (1, 0, 1, 1, 1)),
    (1, 2, 0, (1, 1, 0, 0, 0)),
    (1, 1, 2, (1, 0, 0, 0, 1)),
]

HEADER = r'''import Subtail.RankQueryEnumerationAudit
open Subtail Subtail.RankQuery Subtail.RankQueryCompiler Subtail.RankQueryEnumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def bn (b : Bool) : Nat := if b then 1 else 0

def nn : Option Bool -> Nat
  | none => 0
  | some false => 1
  | some true => 2

def kn : PieceKind -> Nat
  | .core => 0
  | .forward => 1
  | .enter => 2
  | .exit => 3
  | .wrap => 4

def ln : Label -> Nat
  | .F => 0
  | .S => 1
  | .K false => 2
  | .K true => 3

def encLoc : Loc -> List Nat
  | .core i => [0, i]
  | .fresh i => [1, i]

def encColour (c : Colour k) : List Nat :=
  [c.state.val] ++ c.mask.toList.map bn ++ [nn c.next, bn c.root, bn c.isEnd]

def encPiece (p : Piece) : List Nat :=
  [kn p.kind, p.source, p.target, p.lc, p.rc, ln p.label]

def encSeam (s : Nat * Nat * Nat * Nat) : List Nat :=
  [s.1, s.2.1, s.2.2.1, s.2.2.2]

def encD (d : Diagram k) : List (List Nat) :=
  [[d.groups, d.coreVars], d.loc.flatMap encLoc,
   d.states.map Fin.val, d.nextBits.map nn, [bn d.firstBit], encColour d.oldEnd,
   d.pieces.map List.length, d.pieces.flatten.flatMap encPiece,
   d.seams.flatMap encSeam]

def obs (k : Nat) : Observer k :=
  {size := 1, initial := [0], final := [0], allows := fun _ _ => true,
   move := fun _ _ _ _ => [0]}

def noAtoms (k v : Nat) : Clause k :=
  {vars := v, tests := [], equal := [], unequal := [], atoms := []}

def selfAtoms (k a : Nat) : Clause k :=
  {vars := 1, tests := [], equal := [], unequal := [],
   atoms := List.replicate a {observer := obs k, source := 0, target := 0}}
'''

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--python-only', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases: list[tuple[str, str, list]] = []
    for xs in ([], [0], [0, 1], [0, 0]):
        for n in range(5):
            lit = '[' + ','.join(map(str, xs)) + ']'
            cases.append((f'exact-{len(cases)}', f'exactLists ({lit} : List Nat) {n}', lists(xs,n)))
            cases.append((f'upto-{len(cases)}', f'boundedLists ({lit} : List Nat) {n}', upto(xs,n)))
    for k in range(5):
        cases.append((f'masks-{k}', f'(masks {k}).map (fun v => v.toList.map bn)', lists([0,1],k)))
        cases.append((f'colours-{k}', f'(colours {k}).map encColour', colours(k)))
    for n in range(4):
        cases.append((f'pieces-{n}', f'(pieces {n}).map encPiece', pieces(n)))
        cases.append((f'seams-{n}', f'(seams {n}).map encSeam', seams(n)))
    counts=[]
    for i,(k,v,a,b) in enumerate(SHAPES):
        assert a == 0 or v == 1
        clause = f'noAtoms {k} {v}' if a == 0 else f'selfAtoms {k} {a}'
        budget = '{groups := %d, core := %d, perAtom := %d, seamEntries := %d, scalar := %d}' % b
        expected=census(k,v,a,b)
        assert len(expected)==formula_count(k,v,a,b)
        # Independent set check: the literal product must not duplicate a record.
        assert len({json.dumps(x,separators=(',',':')) for x in expected})==len(expected)
        cases.append((f'diagrams-{i}', f'(diagrams ({clause}) ({budget})).map encD', expected))
        counts.append(len(expected))
    if not args.python_only:
        source=HEADER.replace(' * ', ' \u00d7 ')+'\n'
        for name,expression,_ in cases:
            source+=f'#eval IO.println "BEGIN:{name}"\n'
            source+=f'#eval IO.println (reprStr ({expression}))\n'
            source+=f'#eval IO.println "END:{name}"\n'
        with tempfile.TemporaryDirectory(prefix='subtail-enumeration-') as td:
            path=Path(td)/'EnumerationNative.lean'
            path.write_text(source)
            completed=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT/'lean',
                                     text=True,capture_output=True,timeout=240)
            if completed.returncode:
                raise RuntimeError(completed.stdout+'\n'+completed.stderr)
            output=completed.stdout
        for name,_,expected in cases:
            begin, end=f'BEGIN:{name}\n', f'END:{name}\n'
            if output.count(begin)!=1 or output.count(end)!=1:
                raise AssertionError(f'missing/duplicate native marker: {name}')
            actual=json.loads(output.split(begin,1)[1].split(end,1)[0].strip())
            if actual!=expected:
                raise AssertionError(f'field/order discrepancy for {name}: '
                                     f'{len(actual)} native versus {len(expected)} expected')
    digest=hashlib.sha256(json.dumps([(n,e) for n,_,e in cases],
                                   separators=(',',':')).encode()).hexdigest()
    result={'status':'PASS','native_lean':not args.python_only,
            'scope':'Exact finite syntax enumeration; not semantic coverage or unrestricted decision',
            'complete_cases':len(cases),'record_comparisons':sum(len(e) for _,_,e in cases),
            'diagram_cases':len(SHAPES),'diagram_records':sum(counts),'diagram_counts':counts,
            'expected_corpus_sha256':digest,
            'independent_oracle':'Python cartesian products plus closed-form cardinalities'}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()

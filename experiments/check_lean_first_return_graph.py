#!/usr/bin/env python3
"""Literal/native regressions for the Lean first-return graph theorems.

All-length results are the Lean proofs, not these finite experiments. No solver,
network, probabilistic equality, or third-party package is used. --repository
also compares the unchanged candidate's Python graph implementation. --lean
requires actual execution of the pinned Lean definitions and never fakes PASS.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = 'adcc28455fbdd7fd6b60566c272e8d9e7a42335c'
DEPENDENCIES = {
    'border_lab.py': '1144ae52379e0417772e79582269cacd91c5bc17',
    'rank_query_prefix.py': '135d3cb960d07dfddefd74dd255bba289a08af1b',
    'rank_query_graphs.py': '6fcc612e47ef65edbb7ec9ff973a528a422da8e4',
}


def words(bound: int):
    for n in range(bound + 1):
        for bits in product('01', repeat=n):
            yield ''.join(bits)


def borders(w: str) -> list[int]:
    return [h for h in range(len(w) + 1) if w[:h] == w[len(w)-h:]]


def first_return(w: str, m: int) -> bool:
    return 0 < m < len(w) and w.find(w[:m], 1) == len(w)-m


def fixture(w: str, seed: int) -> tuple[list[int], set[tuple[int, int]]]:
    labels = [(seed + j*j + 3*j) % 4 for j in range(len(w) + 1)]
    flags = {(q, t) for q in range(4) for t in range(4)
             if (5*q + 3*t + seed) % 7 < 3}
    return labels, flags


@dataclass(frozen=True)
class Graph:
    # F, S (-1 when absent), K0, K1; masks are integer encodings of boolean functions.
    edges: tuple[tuple[int, int, int, int], ...]
    colours: tuple[tuple[int, int, int, int, int], ...]


def literal(w: str, labels: list[int], flags: set[tuple[int, int]]) -> Graph:
    """String-suffix definition, with no failure-function recursion."""
    edges, colours = [], []
    n = len(w)
    for j in range(n + 1):
        bs = borders(w[:j])
        parent = max((h for h in bs if h < j), default=0)
        dests = [max(h for h in range(n + 1) if (w[:j]+a).endswith(w[:h]))
                 for a in '01']
        mask = sum(1 << q for q in range(4)
                   if any((q, labels[h]) in flags for h in bs))
        edges.append((parent, j+1 if j < n else -1, *dests))
        colours.append((labels[j], mask, int(w[j]) if j < n else -1,
                        int(j == 0), int(j == n)))
    return Graph(tuple(edges), tuple(colours))


def kmp_graph(w: str, labels: list[int], flags: set[tuple[int, int]]) -> Graph:
    """Separate failure-chain computation, also defining full-end fallback."""
    if not w:
        return literal(w, labels, flags)
    n = len(w)
    pi = [0]*(n+1)
    for j in range(2, n+1):
        h = pi[j-1]
        while h and w[h] != w[j-1]:
            h = pi[h]
        if w[h] == w[j-1]:
            h += 1
        pi[j] = h
    edges, colours = [], []
    for j in range(n+1):
        ks = []
        for a in '01':
            h = pi[j] if j == n else j
            while h and w[h] != a:
                h = pi[h]
            ks.append(h+1 if w[h] == a else 0)
        mask, h = 0, j
        while True:
            mask |= sum(1 << q for q in range(4) if (q, labels[h]) in flags)
            if h == 0:
                break
            h = pi[h]
        edges.append((pi[j], j+1 if j < n else -1, *ks))
        colours.append((labels[j], mask, int(w[j]) if j < n else -1,
                        int(j == 0), int(j == n)))
    return Graph(tuple(edges), tuple(colours))


def generate(w: str, m: int, old: Graph) -> tuple[bool, list[int]]:
    """Only old-graph transitions and raw new letters; no extended failure table."""
    if not 0 < m < len(w):
        return False, []
    h = old.edges[m][0]
    cursors = [h]
    for a in w[m:]:
        h = old.edges[h][2+int(a)]
        cursors.append(h)
    return cursors[-1] == m and all(h < m for h in cursors[:-1]), cursors


def surgery(w: str, m: int, labels: list[int], flags: set[tuple[int, int]],
            old: Graph, cursors: list[int]) -> Graph:
    n = len(w)
    edges, colours = [], []
    for j in range(n+1):
        if j < m:
            edges.append(old.edges[j]); colours.append(old.colours[j]); continue
        if j == m:
            p, mask, _, root, _ = old.colours[j]
            ks = tuple(m+1 if a == w[m] else old.edges[m][2+int(a)] for a in '01')
            edges.append((old.edges[m][0], m+1, *ks))
            colours.append((p, mask, int(w[m]), root, 0)); continue
        h = cursors[j-m]
        own = sum(1 << q for q in range(4) if (q, labels[j]) in flags)
        mask = own | old.colours[h][1]
        if j < n:
            ks = tuple(j+1 if a == w[j] else old.edges[h][2+int(a)] for a in '01')
        else:
            ks = tuple(m+1 if a == w[m] else old.edges[m][2+int(a)] for a in '01')
        edges.append((h, j+1 if j < n else -1, *ks))
        colours.append((labels[j], mask, int(w[j]) if j < n else -1, 0, int(j == n)))
    return Graph(tuple(edges), tuple(colours))


def graph_rows(g: Graph) -> list[list[int]]:
    # Native checker uses successor/next-bit encodings zero=None, x+1=Some x.
    return [[e[0], e[1]+1, e[2], e[3], c[0], c[1], c[2]+1, c[3], c[4]]
            for e, c in zip(g.edges, g.colours)]


def check_words(bound: int) -> tuple[dict[str, int], list[dict]]:
    count: Counter[str] = Counter()
    mutation_examples = {}
    for w in words(bound):
        labels, flags = fixture(w, len(w) % 7)
        direct = literal(w, labels, flags)
        assert direct == kmp_graph(w, labels, flags)
        count['literal_kmp_vertices'] += len(w)+1
        count['words'] += 1
        for m in range(1, len(w)):
            old = kmp_graph(w[:m], labels[:m+1], flags)
            hit, cursors = generate(w, m, old)
            expected = first_return(w, m)
            assert hit == expected, (w, m, cursors)
            count['generator_iff_cases'] += 1
            if not hit:
                count['rejected_generator_cases'] += 1
                continue
            actual = surgery(w, m, labels, flags, old, cursors)
            assert actual == direct, (w, m, actual, direct)
            assert cursors[1:] == [e[0] for e in direct.edges[m+1:]]
            for j in range(m+1, len(w)+1):
                forbidden = bool(direct.colours[j][1] & (1 << labels[j]))
                guard = ((labels[j], labels[j]) in flags or
                         bool(old.colours[cursors[j-m]][1] & (1 << labels[j])))
                assert guard == forbidden
                count['fresh_guard_equivalences'] += 1
            count['first_return_graphs'] += 1
            count['first_return_vertices'] += len(w)+1
            count['overlapping_returns'] += len(w) < 2*m
            count['singleton_extensions'] += len(w) == m+1
            count['repeated_cursor_values'] += len(set(cursors[1:])) < len(cursors)-1
            # Retained mutants show why endpoint/wrap/current-column details matter.
            a = int(w[m])
            if old.edges[m][2+a] != direct.edges[-1][2+a]:
                mutation_examples.setdefault('omit_endpoint_wrap', dict(word=w, old_length=m,
                    wrong_target=old.edges[m][2+a], correct_target=direct.edges[-1][2+a]))
            if old.colours[m] != direct.colours[m]:
                mutation_examples.setdefault('keep_old_endpoint_colour', dict(word=w, old_length=m))
            for j in range(m+1, len(w)+1):
                h = cursors[j-m]
                if old.colours[h][1] != direct.colours[j][1]:
                    mutation_examples.setdefault('omit_new_column', dict(word=w, old_length=m,
                        new_cut=j, wrong_mask=old.colours[h][1], correct_mask=direct.colours[j][1]))
    assert len(mutation_examples) == 3
    return dict(sorted(count.items())), [dict(mutation=k, **v) for k, v in sorted(mutation_examples.items())]


def repository_checks(bound: int) -> dict:
    # Pin comparisons so altered implementations cannot inherit a past audit.
    for name, expected in DEPENDENCIES.items():
        data = (ROOT/'experiments'/name).read_bytes()
        actual = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual != expected:
            raise RuntimeError(f'Reviewed dependency changed: {name}: {actual}')
    from border_lab import Instance
    from rank_query_prefix import Reference
    from rank_query_graphs import graph_from_reference, literal_graph, local_extension
    count: Counter[str] = Counter()
    for w in words(bound):
        if not w:
            continue
        for seed in (0, 2, 5):
            labels, flags = fixture(w, seed)
            # No run premise is imposed in the structural equality theorem.
            I = Instance(delta=((0, 0),)*4, final=frozenset(), flags=frozenset(flags))
            ref = Reference(w, tuple(labels))
            g = graph_from_reference(I, ref)
            assert g == literal_graph(I, ref)
            direct = literal(w, labels, flags)
            assert tuple((c.state, c.forbidden, int(c.next_bit) if c.next_bit else -1,
                          int(c.root), int(c.end)) for c in g.colours) == direct.colours
            edge_rows = tuple((g.target(j, 'F'), j+1 if j < len(w) else -1,
                               g.target(j, 'K0'), g.target(j, 'K1')) for j in range(len(w)+1))
            assert edge_rows == direct.edges
            count['base_graphs'] += 1
            for m in range(1, len(w)):
                if not first_return(w, m):
                    continue
                gg, origins = local_extension(I, Reference(w[:m], tuple(labels[:m+1])),
                                               ref, require_safe=False)
                assert gg == g
                hit, cs = generate(w, m, kmp_graph(w[:m], labels[:m+1], flags))
                assert hit and list(origins) == cs[1:]
                count['candidate_surgery_graphs'] += 1
    return dict(status='PASS', max_word_length=bound, counts=dict(sorted(count.items())),
                dependency_git_blobs=DEPENDENCIES,
                scope='Structural equality on arbitrary labels; require_safe=False is explicit.')


def native_lean(bound: int) -> dict:
    lean_dir = ROOT/'lean'
    version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=lean_dir,
                             text=True, capture_output=True, check=True).stdout
    if 'version 4.33.1,' not in version:
        raise RuntimeError('Expected pinned Lean 4.33.1, got '+version)
    lines = ['import Subtail.FirstReturnColours',
             'open Subtail Subtail.FirstReturnGraph',
             'set_option maxRecDepth 8192', 'set_option maxHeartbeats 20000000',
             'def testLabel (seed j : Nat) : Fin 4 :=',
             '  ⟨(seed+j*j+3*j)%4, Nat.mod_lt _ (by decide)⟩',
             'def testCol (seed : Nat) (q t : Fin 4) : Bool :=',
             '  decide ((5*q.val+3*t.val+seed)%7 < 3)',
             'def encodeRow (ce : Colour 4 × Edges) : List Nat :=',
             '  let (c,e) := ce',
             '  let maskN := (List.finRange 4).foldl (fun s q => s + (if c.2.1 q then 2^q.val else 0)) 0',
             '  [e.1, (e.2.1.map (·+1)).getD 0, e.2.2.1, e.2.2.2, c.1.val, maskN,',
             '    (c.2.2.1.map (fun b => if b then 2 else 1)).getD 0,',
             '    if c.2.2.2.1 then 1 else 0, if c.2.2.2.2 then 1 else 0]',
             'def literalRows (w : Word) (seed : Nat) : List (List Nat) :=',
             '  (List.finRange (w.length+1)).map fun j => encodeRow (literalGraph w (testCol seed) (testLabel seed) j)',
             'def surgeryRows (w : Word) (m seed : Nat) : List (List Nat) :=',
             '  (List.finRange (w.length+1)).map fun j => encodeRow (surgeryGraph w m (testCol seed) (testLabel seed) j)',
             'def hitCheck (w : Word) (m : Nat) : Bool :=',
             '  decide (m < w.length) && (cursor w m (w.length-m) == m) &&',
             '    (List.range (w.length-m)).all (fun d => decide (cursor w m d < m))',
             'def checkRows (rows : List (Word × Nat × List (List Nat) × List Bool)) : IO Unit := do',
             '  for (w,seed,expected,hits) in rows do',
             '    unless literalRows w seed == expected do',
             '      throw (IO.userError s!"literal graph mismatch: {w} {seed}")',
             '    unless (List.range (w.length-1)).map (fun i => hitCheck w (i+1)) == hits do',
             '      throw (IO.userError s!"first-hit mismatch: {w}")',
             '    for i in List.range (w.length-1) do',
             '      let m := i+1',
             '      if hitCheck w m then',
             '        unless surgeryRows w m seed == expected do',
             '          throw (IO.userError s!"surgery graph mismatch: {w} {m} {seed}")']
    rows, count = [], Counter()
    for w in words(bound):
        for seed in (0, 2, 5):
            labs, fs = fixture(w, seed)
            expected = graph_rows(literal(w, labs, fs))
            hits = [first_return(w, m) for m in range(1, len(w))]
            lw = '['+','.join('true' if a == '1' else 'false' for a in w)+']'
            lh = '['+','.join('true' if b else 'false' for b in hits)+']'
            rows.append(f'({lw}, {seed}, {expected}, {lh})')
            count['literal_graphs'] += 1
            count['literal_vertices'] += len(w)+1
            count['generator_iff_cases'] += len(hits)
            count['first_return_graphs'] += sum(hits)
    for i in range(0, len(rows), 32):
        lines.append('#eval checkRows ['+','.join(rows[i:i+32])+']')
    scratch = ROOT/'tmp'/'lean-first-return-graph-regressions.lean'
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch.write_text('\n'.join(lines)+'\n', encoding='utf-8')
    done = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=lean_dir,
                          text=True, capture_output=True)
    if done.returncode:
        raise RuntimeError(done.stdout+done.stderr)
    return dict(status='PASS', toolchain='leanprover/lean4:v4.33.1',
                max_word_length=bound, counts=dict(sorted(count.items())))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    parser.add_argument('--repository', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Run with assertions enabled (no -O)')
    counts, mutations = check_words(10)
    out = dict(status='PASS', base_commit=BASE, python_max_word_length=10,
               counts=counts, rejected_mutations=mutations,
               repository_comparison='NOT_RUN', native_lean='NOT_RUN',
               limits=['Finite regressions do not establish the all-word graph theorem.',
                       'Kernel-checked proof dependencies and semantic readback are separate evidence.',
                       'No uniform query compiler or unrestricted subtype decision is verified.'])
    if args.repository:
        out['repository_comparison'] = repository_checks(7)
    if args.lean:
        out['native_lean'] = native_lean(7)
    text = json.dumps(out, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()

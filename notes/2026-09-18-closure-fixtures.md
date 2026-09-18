# Adversarial fixtures for the Closure Lemma: joint conjunction, shared generator, two-atom unions

Date: 2026-09-18. Workstream A017 support (C080, stage 4; issue #32, tracker #34).
Base main: `d1fdcfb`. Author: Claude (Claude Code session), instructed by the
repository owner. Checker: [check_closure_fixtures.py](../experiments/check_closure_fixtures.py);
result: [closure-fixtures.json](../results/closure-fixtures.json).

**Status: bounded adversarial evidence for the implementation as written; no
discrepancy found. Nothing here proves the Closure Lemma or changes the
CANDIDATE status of C080 or of Problem 1.7.** A found discrepancy would have
refuted `rank_preimage.py` as written and would have been posted on #32 with
the exact query, base and commit before any fix. None was found.

## 1. What is judged and by what

The compiler under test is imported and never modified: `rank_preimage.py`
(`iter_diagrams`, `extract_diagram`, `compile_diagram`, `reconstruct_reference`,
`finish_queries`), `rank_preimage_core.py` (`model`, `path`, observers),
`rank_query_graphs.literal_graph`, `rank_query_prefix.Reference`. The
all-length oracle `rank_frontier_oracle.fixed_reference_query` is a second
implementation and is compared where it completes (state cap 20,000).

Everything used to judge them is written independently in the checker:

* `accepts(G, O, s, t)`: breadth-first search on `(vertex, control)`, reading
  observer tables directly; `truth(G, Q)`: exhaustive assignments of the query
  variables filtered by unary tests, `=`/`≠`, then `accepts` per path atom.
* `literal_safe(I, rho, labels)`: reverse-run consistency, no `Bad` state, and
  the literal border-chain flag check on every prefix `rho[:j]` against every
  border `rho[:b]` (diagonal and empty border included). No prefix function.
* `extensions(I, B, max_len)`: EVERY safe extension `C` of the base `B` with at
  most `max_len` new letters such that `B.word` reoccurs as a suffix of
  `C.word` and does not reoccur ending strictly earlier (`literal_first_return`;
  overlapping returns and `L = 1` included), generated from the instance's
  incoming-transition table, not from the compiler's cursor walk.

For each fixture `(I, B, φ)` the checker records:

1. **Brute force.** `found = {C ∈ extensions : truth(P(C), φ)}`; `YES` with the
   shortest length, or `NONE_UP_TO_n`, which is NOT a negative.
2. **Oracle.** The all-length fixed-base oracle's `YES`/`NO`/`UNKNOWN`; `NO`
   against a brute-force `YES` is a discrepancy.
3. **Completeness certificates.** For up to six found `C`: the compiler's
   `model(P(C), φ)` must agree with `truth` (else `compiler_evaluator_disagrees`);
   the extracted diagram `D` must pass a structural membership check against
   the compiler's own diagram enumerator (each atom's kind/label sequence is
   offered by `path_shapes` up to the zero-length core/forward pieces that
   extraction omits, and the mark order passes the enumerator's filters;
   `enumerator_accepts`, else `certificate_diagram_not_enumerated`); the compiled
   clause must have weight `≤ U_k(weight φ)`; it must be satisfiable on `P(B)`
   (forward direction, else `forward_direction_failed`); and its model must
   reconstruct (soundness, below). Where the same clause is also satisfiable on
   a different base `B'`, the reconstruction from `P(B')` is checked too.
4. **Soundness.** Every satisfied compiled clause is handed to
   `reconstruct_reference`; the result must be a safe first-return extension of
   `B` (literal predicates), agree with `B` on word and labels, and satisfy `φ`
   under `truth` on its literal graph (else `unsound_clause`).
5. **Exhaustive unions** (where enabled). The compiled `Pre_I(φ)` is enumerated
   clause by clause under a deterministic work cap; `EXHAUSTED` unions must
   agree with the oracle and must contain a satisfiable clause whenever brute
   force found an extension; `UNKNOWN_WORK` unions contribute only the soundness
   and weight checks of their enumerated prefix. A time cap would be
   nondeterministic and is recorded as a discrepancy, so the saved result is
   byte-reproducible.

The one-state toy `Instance(((0,0),), ∅)` has no accepting state; its fixtures
run with `require_final=False` (the compiler tests' graph-mechanism mode: the
references are not terminal witness suffixes). The random terminal fixtures and
the ultimate-cut fixture use real terminal instances with the accepting
requirement on `r_0`.

## 2. Fixture families (quick mode as replayed in CI)

**Joint conjunction (contract 1).**

* `S`-lengths `(2,)`, `(3,)`, `(2,3)` on `P("0")`: the two single atoms have
  extensions (shortest 2 and 3); the conjunction has none up to 6 letters and
  the oracle says `NO`. A 900-clause sample of the joint compiled union has no
  satisfiable clause.
* Twelve separately-`YES`/jointly-`NO` pairs of exact observers (`end→root` and
  `root→end`, length `≤ 3`), six on base `"0"` and six on `"00"`, found by an
  exhaustive oracle search and hard-coded (`INCOMPATIBLE_PAIRS`; 24 pairs, all
  in full mode). For each pair the checker re-verifies the three oracle
  statuses, finds brute-force extensions for each single atom and certifies
  them, and enumerates the joint union under a 300,000-step work cap: 1,560 to
  9,494 clauses each, none satisfiable.
* Two two-atom loop-observer unions (`('S',)|('F','S','K1')` and
  `('S',)|('K0',)`, both `end→root`, base `"0"`): loop observers re-enter the
  strip repeatedly; 48,764 and 57,690 clauses enumerated under the work cap,
  none satisfiable, oracle `NO`, no extension up to 6 letters. No loop pair is
  separately-`YES`/jointly-`NO`, which is why the exact-observer pairs exist.
* Zero-length shared endpoint on `P("00")`: an empty-path atom and an `F`-loop
  atom on the same two variables, forced equal. The union is EXHAUSTED: 5,256
  clauses, 3 satisfiable, all three reconstruct to safe first returns; brute
  force and oracle both `YES` (shortest 3).

**Shared generator (contract 2).**

* Shared origin, distinct marks: `S²` and `S³` from the root to two distinct
  marks `u ≠ v`, both with `F` exits to the root, plus a `K0` edge from `v` to
  the end. Brute force `YES` (shortest 4); every certificate reconstructs to one
  extension.
* Singleton wrap (`L = 1`): base `"00"`, a `K0` self-loop atom at the end
  vertex; the one-letter extension `"000"` is found and certified; 76,123
  union clauses enumerated under the cap, none satisfiable. The certificate's
  diagram passes the structural membership check but its clause was not among
  the enumerated clauses, so this union is `UNKNOWN_WORK`, not a miss;
  completeness for this fixture rests on the forward certificate alone.
* Return at the ultimate accepting cut: the `(1,1)` modular family, witness
  `1010`, reversed `0101`, base `"01"` returning exactly at the final position;
  the finishing query that the complete witness satisfies is the fixture. Brute
  force finds the witness itself (length 4); 40,684 union clauses enumerated,
  one satisfiable, reconstructing soundly.
* Seam controls: an exact three-letter observer split across marks by a second
  atom's `F` exit and `S` edge. `YES`, shortest 3, certificates sound.

**Coloured terminal instances.** Twelve random terminal instances with
`k ∈ {2,3,4}`, random flags, bases taken from reversed prefixes of genuine
witnesses, and two random table observers each: brute force up to 5 letters,
oracle, forward certificates and soundness. Three `YES` (shortest 2, 2, 3),
nine `NO`.

## 3. Executed result

`python3 experiments/check_closure_fixtures.py --quick --output results/closure-fixtures.json`
(seed `2026091832`, work cap 1,500,000; about 137 s), run twice with
byte-identical output; status `PASS`, discrepancies `[]`.

| Count | Value |
|---|---|
| Fixtures recorded | 35 (34 fixtures and one union sample) |
| Safe first-return extensions enumerated by brute force | 149 |
| Certificate diagrams accepted by the compiler's enumerator | 54 |
| Forward certificates (compiled clause true on `P(B)`) | 54 of 54 |
| Sound reconstructions (one safe first return satisfying `φ`) | 59 |
| Exhausted unions | 1 (5,256 clauses, 3 satisfiable) |
| Work-capped unions | 16 (plus one sampled) |
| Compiled clauses checked against `U_k(T)` | 297,083, all within the bound |
| Oracle `YES` / `NO`, all consistent with brute force | 10 / 24 |
| Separately-`YES`/jointly-`NO` pairs confirmed | 12 |
| Other-base reconstructions | 1 (sound; different length) |

## 4. What this does and does not show

* Every brute-force extension of every fixture yields a diagram that passes
  the structural membership check of the compiler's enumeration and compiles
  to a clause that is true on the base graph and reconstructs to exactly one
  safe first return. No compiled clause
  seen (297,083) exceeded the weight bound or reconstructed to anything other
  than a safe first-return extension satisfying the query.
* Joint conjunction is tested only by finite prefixes of the joint unions
  (except the exhausted zero-length fixture): the checker shows that no
  enumerated clause is satisfiable, not that the whole union is unsatisfiable.
  The all-length oracle's `NO` is the only complete negative in each record.
* Brute force is capped at 4–7 new letters. `NONE_UP_TO_n` is bounded
  evidence; every `NO` verdict is the oracle's.
* Full mode (`--full`: all 24 incompatible pairs, 14 loop pairs, 30 terminal
  fixtures, no work caps) is a long local run and is not byte-comparable to
  the saved result.
* The independent evaluator shares the query grammar's semantics with the
  compiler by construction; agreement on 54 certificate graphs and 59
  reconstructed graphs is a regression, not a proof of the semantics.

## 5. Handoff

The obstruction the fixtures were built to expose (a compiled clause satisfied
by two different extensions, or a jointly unsatisfiable conjunction with a
satisfiable compiled clause) did not appear. The next discriminating steps
are: exhaust at least one two-atom union with a non-trivial mark set (the
two-loop unions exceed 180,000 clauses and 120 s; a smarter enumerator or a
smaller instance is needed), and prove the two directions of `ClosureFor` for
an executable `preimage` in Lean against the pinned statement of
[RankQuery.lean](../lean/Subtail/RankQuery.lean) (issue #27, stage 4a), where
the fixtures here serve as `#guard`-style regressions for that function.

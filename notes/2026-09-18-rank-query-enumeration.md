# Exact finite enumeration of bounded rank-query diagrams

Date: 2026-09-18. Actor: ChatGPT `diagram-enumeration-20260918`.
Workstream A018 supporting A017/C080, stage 4b; issue #28, tracker #34.
Base: `91911abb786349d2d4d4a37f5ebc20ef4995fdad`.
Branch: `lean/diagram-enumeration-2026-09-18`.

This is a disjoint contribution to the missing forward coverage theorem, not a
new proof of the unrestricted decision. It leaves the compiler, reverse proof,
physical-mark work, core definitions, default imports and ledgers unchanged.

## 1. Route and exact scope

The reverse theorem already establishes that a satisfying compiled diagram
reconstructs one common safe first-return extension. Its compiler accepts a
supplied finite list of diagrams. To obtain a complete uniform preimage we need:

1. finitely many syntax choices for a query and explicit budget, generated effectively;
2. exact inclusion of every diagram satisfying the stated syntax bounds;
3. a proof that every real satisfying first-return extension has such a diagram;
4. the quantitative weight estimate needed for the advertised bound, and the
   remaining integration of the final decision theorem.

This module completes (1) and (2), composes them with the existing reverse
correctness, and gives a formal interface for (3). It does NOT prove (3), (4),
`ClosureFor`, or unrestricted entailment. Merely increasing syntax budgets is
not an all-input negative decision procedure.

The independently owned physical-mark and portal-transport modules are not
modified or imported. There is no competing reconstruction proof here.

## 2. What is enumerated

The implementation uses the existing `RankQueryCompiler.Diagram k` unchanged.
A `Limits` value has five natural-number components:

| Component | Exact bound |
|---|---|
| `groups` | Positive number of ordered fresh mark groups, at most this value |
| `core` | Number of indexed old/core variables, at most this value |
| `perAtom` | Length of each atom's piece list, at most this value |
| `seamEntries` | Length of the shared seam-control list, at most this value |
| `scalar` | Every natural-number piece field and seam coordinate is strictly below this value |

Locations use indices smaller than the actual `coreVars`/`groups`, not the
larger caps. The location list has exactly `c.vars` entries; states and next
bits have exactly `D.groups` entries; the outer piece list has exactly
`c.atoms.length` entries. States range over `Fin k`, masks over all `Vector Bool
k`, next bits over `none`, `some false`, `some true`, and edge labels/kinds over
the existing finite alphabets. All these choices are explicit finite products.

The proposition `Bounded c b D` states those constraints WITHOUT referring to
enumerator membership, `validDiagram`, query satisfaction or a reference word.
Thus its use as a specification is not circular.

No bound here concerns the length of B, C, a physical interval, an observer
walk, or a subtype separating address. A diagram can constrain arbitrarily long
physical intervals using finite observers. The runtime enumeration reads the
finite clause and its syntax caps, not a graph or any candidate reference.

## 3. Exact membership and construction

`exactLists xs n` enumerates length-n lists over the supplied finite alphabet.
Its induction proves

    ys in exactLists xs n
      iff length(ys) = n and every entry belongs to xs.

`boundedLists` takes the union for lengths zero through its bound. Masks are
converted into vectors using a checked equality of lengths; no proof-valued
choice is used to manufacture executable vectors.

`mem_pieces` and `mem_seams` prove exact coordinate bounds. Their enumeration is
intentionally redundant: a meaningless coordinate or label for one piece kind
is still permitted within its cap. The EXISTING `validDiagram` performs the
kind-specific and chain checks. Extra candidates cannot defeat reverse
soundness; omitting a necessary candidate could defeat coverage. This design
favours a transparent superset over an unproved optimization.

The main unconditional theorem is:

```lean
mem_diagrams (c : Clause k) (b : Limits) (D : Diagram k) :
  D ∈ diagrams c b ↔ Bounded c b D
```

Each direction explicitly decomposes or assembles the finite product. It
includes zero bounds, empty piece lists, empty seam lists and empty alphabets.
There is no quotient identifying diagrams or words with a common profile.
Duplicates in a supplied helper alphabet remain duplicates; no `DecidableEq`
instance for the function-containing query clauses is required.

`mem_validDiagrams` adds exactly the existing compiler's Boolean validity
condition. `mem_preimageClause` gives exact clause membership:

    P in preimageClause I c b
      iff exists D, Bounded c b D and compileDiagram I c D = some P.

This is a total finite definition for every finite syntax budget. We do not
claim efficient execution on large budgets.

## 4. Connecting to actual first-return semantics

`preimage I budget phi` enumerates and compiles the diagrams for every clause
of the query, using the supplied computable budget function. The theorem
`preimage_sound` instantiates the existing `RankQuerySound.closure_reverse`:

    SafeReference I B ->
    Sat (prefixGraph I B) (preimage I budget phi) ->
      exists C, FirstReturnExt I B C and Sat (prefixGraph I C) phi.

This holds for ANY syntax budget, not only a semantically sufficient one.
There is no `TerminalFinals` assumption in this inherited local statement.
It preserves the same common generated reference used in the upstream proof;
this module does not choose a different reference per atom.

On any finite query graph G, `sat_preimageClause_iff` gives the exact scope of
finite exhaustion:

    Sat G (preimageClause I c b)
      iff exists D,
        Bounded c b D and validDiagram I c D = true
        and SatClause G (compileValid I c D).

A negative answer here excludes all compiled diagrams IN THAT SYNTAX BUDGET.
It cannot exclude other budgets until semantic coverage is established.

## 5. The remaining extraction obligation, explicitly typed

The module defines, but does not prove, `DiagramCoverage I budget`:

    for every B,C,
      SafeReference I B -> FirstReturnExt I B C ->
      for every clause c,
        SatClause (prefixGraph I C) c ->
        exists D,
          Bounded c (budget c) D
          and validDiagram I c D = true
          and SatClause (prefixGraph I B) (compileValid I c D).

The three conclusions require the SAME D, and the final SatClause requires
ONE joint assignment for its whole conjunction. A proof giving separate
assignments for different atom pieces is insufficient.

`forward_of_coverage` and `preimage_iff_of_coverage` are proved CONDITIONAL
compositions. They take `DiagramCoverage I budget` as an explicit argument.
No axiom, typeclass instance or default implementation supplies that argument.
The latter theorem gives the semantic biconditional once extraction is proved;
it does not give the weight part of `ClosureFor`.

The next forward proof should use the actual product-simple runs and physical
marks to construct D. It must bound all five fields from the INPUT CLAUSE,
choose consistent seam controls, establish the exact `validDiagram` guard,
and construct a joint base-graph model of `compileValid`. A physical-mark count
alone does not supply the piece, core-name and seam bounds or that model.
Old-graph origins can coincide even when physical fresh marks are distinct;
that distinction must be retained. Overlapping returns, a one-vertex extension,
and a full return at the final cut must all remain covered.

The redundant enumeration means the extractor need not reproduce Python's
particular generation order or quotienting heuristics. This checker does NOT
prove that the Python `iter_diagrams` enumerator is complete. It provides an
alternative whose exact finite syntactic coverage is checked in Lean.

## 6. Boundary proofs and independent executable census

The audit module proves 11 boundary statements: zero-length lists over empty
alphabets, positive-length impossibility for empty alphabets, duplicate
preservation, zero/one piece and seam cases, mask and colour cardinalities,
zero-group exclusion, out-of-range controls, and outer atom-count mismatch.
The concrete kernel proofs use `decide` or definitional reduction, not
`native_decide` or a native-evaluation axiom.

The independent Python checker uses `itertools.product`, not a translation of
the Lean inductive membership proof. It computes closed-form cardinalities
separately and compares every field of every native Lean output, including
ordering, nested lengths and repeated entries. It also checks uniqueness of
the encoded diagram records in its complete small diagram corpora.

The test corpus consists of 70 complete finite enumeration comparisons,
including 13,968 diagrams in 12 budget shapes, 17,435 records in total. The
shape counts are

    0, 0, 144, 144, 432, 1008, 1152, 1152, 3024, 6048, 720, 144.

These are explicit SYNTAX oracles, not tests of witness existence or of
unrestricted semantic extraction. `--python-only` is labelled as such and does
not claim any native Lean execution. The normal mode requires Lean, and raises
an error on a build error, timeout, missing marker or field discrepancy.

The corpus digest is
`1d29464ccd405f818ba4f6c8b990dbc9de3fd5977b1d955ca901fc0e71ad46c4`.

## 7. Validation record

The final checked commit is `fb5032ceaace969aea7cbf5fc0a286f5e333f6cd`.
Run `35397001335`, job `105768033700`, completed successfully: both modules
compiled, bundled kernel replay passed, all 51 named declaration dependency
audits passed (29 theorems, 20 definitions, one structure and one abbreviation),
and both native census executions agreed field-by-field with the independent
oracle. The two executions used Python hash seeds 17 and 91 and returned
byte-identical JSON. The existing Lean-core checks and unchanged-evidence
check also passed. The exact evidence is recorded in
`results/lean-rank-enumeration.json`. No local Lean installation was available;
all actual Lean compilation, kernel replay and native comparisons occurred in
GitHub Actions with the repository's pinned toolchain. Local Python runs are
identified separately.

Four draft failures are retained in the branch history. Initial drafts used
unavailable List monadic notation and an invalid bounded-quantifier spelling;
subsequent repairs replaced over-broad simplifier calls with explicit
membership witnesses and normalized record projections before arithmetic.
The theorem statements and intended runtime enumeration were not weakened.
At `6375746`, both Lean modules compiled, kernel replay and all 51 named public
dependency audits passed. The native harness then found its OWN delimiter bug:
`END:upto-1` also counted the prefix of `END:upto-11`. Requiring a full marker
line repaired that parser without changing the expected corpus or Lean code.
All final evidence must refer to the repaired runner revision, not a failed run.

Reproduction from a checkout containing the branch:

```sh
cd lean
lake build +Subtail.RankQueryEnumerationAudit
lake env leanchecker Subtail.RankQueryEnumerationAudit
cd ..
PYTHONHASHSEED=17 python3 experiments/check_rank_enumeration.py --output /tmp/enum-a.json
PYTHONHASHSEED=91 python3 experiments/check_rank_enumeration.py --output /tmp/enum-b.json
cmp /tmp/enum-a.json /tmp/enum-b.json
python3 scripts/check_lean.py
```

The separate workflow audits the dependency closure of all named new
public declarations. Runtime definitions may not depend on Classical.choice;
proof theorems may use the standard propext, Quot.sound and Classical.choice.
Custom, unfinished and native-evaluation axioms are rejected. Counts of named
declarations do not claim separate enumeration of every generated projection
or recursor; imported dependencies are covered through kernel replay and the
transitive axiom reports of the named endpoints.

## 8. Integration and status

The branch is a disjoint, additive checkpoint, not a force update of main.
The shared import aggregator, canonical workstream registry, C080 status,
other authors' proof files and pre-existing workflows are unchanged. The
coverage worker can import this module without changing the original Diagram
or compiler interfaces. Default imports and ledger integration are left to
the coordinating author after the issue handoff.

Completed contribution: exact finite diagram syntax generation, exact scoped
compiled-query semantics, and unconditional inherited reverse soundness.
Remaining: actual bounded extraction (`DiagramCoverage`) for a concrete
computable budget, quantitative weight proof and the remaining end-to-end
semantic/decision composition. No human referee or independent re-proof of the
upstream closure theorem was performed. This note is an author readback.

# Independent semantic readback of the expression entailment decision

Date: 2026-09-19.
Session: `entailment-review-20260919`.
Workstreams: A010/A013/A018; C029/C031 and the qualitative stage-6 part of
C080; issues #31/#34/#37.

## Review boundary and verdict

I reviewed the final composition source at parent commit
`9f7d57cbd695a68dd52a69dc81b8446bd7c85d9e`, whose parent is the requested
composition base `23165f884fc295f04973189b55e78f068de44b41`. The new source is
`lean/Subtail/EntailmentDecision.lean`; `lean/Subtail.lean` now imports the
finite-expression core and this decision module, while
`ExpressionNormalizationAudit` remains separate.

This is a source and statement readback. I did not build Lean, replay the
kernel, run the declaration/runtime axiom audit, run native regressions, or
inspect another worker's checkout. Fresh combined validation is therefore
PENDING at this review revision. The review inherited the separate
normalization readback and the pinned C029 readback; it is cross-session source
review, not a blind derivation, human referee report, or duplicate
normalization implementation.

**Result:** I found no semantic blocker in the final composition. The source
matches the intended arbitrary-tree Problem 1.7 contract, with the explicit
finite syntax and Boolean entry points described below. No satisfiability,
finite-model, regular-model, witness-bound, U/F, C030, or caller-supplied
absorption premise was introduced.

## Pinned source identities

The following SHA-256 values are computed from the exact files at
`9f7d57cbd695a68dd52a69dc81b8446bd7c85d9e`:

| File | SHA-256 |
|---|---|
| `lean/Subtail/EntailmentDecision.lean` | `a899b12e1d2b968053a0062a1600c9d368fe5c16f1ba3b74aef591b311088f59` |
| `lean/Subtail/ExpressionNormalization.lean` | `6e69fa21ebf0a0ffa65f78c976eb6681a85e9c9778cf96e57d16fb86b1285b82` |
| `lean/Subtail/TreeSemantics.lean` | `8b08b74d08bac48454f99f0241eb066ef6b218334641f284bc26423957a78f2e` |
| `lean/Subtail/SubtypeTerminalBridge.lean` | `4a6fb1e783fdf052c1ac61bfd24aae9dbc5d1c441961e41d7cd02f434d57b751` |
| `lean/Subtail/InfiniteDecision.lean` | `d9679db4b52062a707f74c4a7198137f608660930e3f4a2d868ab4efac40228d` |
| `lean/Subtail/RankQueryDecision.lean` | `51fef747bb443d313559e57d8fb8e3c1ce68b804eb4883a7d504e2945da5bd8a` |
| `lean/Subtail.lean` | `39f505dc465561ea82f90856502fcb23dfc84f48908377acb62052a7e5e23460` |

The new module has 95 lines. Its declarations are at the following pinned
source locations: `rawNormalizedEntailsCheck` lines 18–20,
`rawNormalizedEntailsCheck_correct` lines 22–32,
`normalizedEntailsCheck` lines 46–52,
`normalizedEntailsCheck_correct` lines 54–76,
`entailsCheck` lines 80–82, and `entailsCheck_correct` lines 86–89.

## Semantic input and valuation contract

The formal input is finite syntax, not a model presentation:

```text
G : List (Expr n × Expr n)
s t : Expr n
Expr := var (Fin n) | bot | prod Expr Expr
```

`ExpressionNormalization.ExprModels` and `ExprEntails` quantify over every
valuation `Fin n -> Tree`. `Tree.nodes` is an arbitrary `Word -> Prop` with a
prefix-closure proof. It is not a finite set, regular language, decidable
membership oracle, or bounded-depth tree. `TreeSemantics.product` inserts the
root and maps the two child subtrees under `false` and `true`, while `bottom`
has no product nodes. `Below` is pointwise set inclusion. This is the same
product-node representation of the memo's arbitrary, possibly infinite types;
the earlier C001/TreeSemantics bridge is inherited rather than re-proved in
this review.

`ExprEntails G s t` has the required direction:

```text
forall rho, ExprModels G rho -> Below (eval rho s) (eval rho t)
```

Thus the final theorem decides `s <= t`, not its reverse, and quantifies over
all satisfying valuations. The input premises are exactly `G`; the queried
inequality is not added to `G`.

## Normalization link

The inherited `ExpressionNormalization.normalized G s t` is the definition
list for every product occurrence and the optional bottom slot, followed by
the original list `G` mapped to variable inequalities. It does not append a
constraint for `s <= t`. Duplicate product occurrences still receive distinct
defining slots; repeated syntax may reference the first slot, but every slot
has both defining inequalities. Query-only variables and the `n = 0` constant
cases are covered by the proved positive output count.

The exact theorem is:

```text
normalize_entails_iff G s t :
  ExprEntails G s t iff
  Entails (normalized G s t)
    (naming G s t).ref s (naming G s t).ref t
```

Its extension/restriction arguments preserve the values of all original
variables and the meanings of both query expressions. The same finite address
is preserved in the separate separating-address theorem. Therefore the final
module can use the normalized references without adding a model-finiteness or
query-premise assumption.

## Exact normalized branch composition

At lines 18–20, `rawNormalizedEntailsCheck` binds one instance:

```text
I := summaryInstance C a b
!(infiniteWitnessCheck I || terminalWitnessCheck (terminalize I))
```

This is the same `I` in both branches and in the semantic bridge. The source
does not reconstruct the summary instance independently for the terminal
branch. The Boolean is the negation of the disjunction of the two
non-entailment certificates.

The checked bridge has the exact proposition:

```text
not Entails C a b iff
  InfWitness (summaryInstance C a b) or
  terminalWitnessCheck (terminalize (summaryInstance C a b)) = true
```

`SummaryAutomaton.not_entails_iff_witness` first connects arbitrary-tree
non-entailment to an actual finite separating address. Its `Bad` bit keeps
UNSAT inside the same witness predicate; it does not assume satisfiability.
The canonical model proof supplies all forced roots and prefix seeds, so the
bridge does not replace arbitrary trees with finite or regular models.

`SubtypeTerminalBridge.summary_absorbing` discharges the only hypothesis needed
by the C029 Boolean: for every enumerated summary state, not only reachable
states, a final state's successor is final and has an empty incoming flag
column. It obtains this from `summary_absorbs` after rewriting the exact
`summary_step` relation. The parent theorem applies
`infiniteWitnessCheck_correct` with precisely this proof at lines 25–29.
No absorption premise is exposed by `rawNormalizedEntailsCheck_correct`.

The terminal side is also discharged internally. `terminal_summary_check`
applies `terminalWitnessCheck_correct` to `terminalize I` using
`terminalize_terminal I`; this terminality proof is unconditional for the
constructed terminalized instance. `terminalize` prunes unsafe source/target
edges before selecting final states, and `terminalFinal` tests the original
final bit. The source therefore retains the original final semantics and does
not silently promote a nonfinal sink.

The theorem at lines 22–32 rewrites the bridge with
`infiniteWitnessCheck_correct` and then exhausts the two Boolean branch values.
The resulting cases prove exactly that the negated Boolean disjunction is true
iff `Entails C a b`. The proof uses `classical` only in this erased theorem;
the runtime definition has no classical branch.

## Total normalized frontend and shortcuts

`normalizedEntailsCheck` is a total finite Boolean. Its four branches are
semantically sound:

1. `a = b` returns true by `entails_self`, since `Below` is reflexive.
2. A listed `Constraint.leq a b` returns true by applying that premise to any
   model. This checks an existing input premise; it does not add the query.
3. An executable `satCheck C = false` returns true. The proof uses
   `satCheck_correct` to show that no model exists, so entailment is vacuous.
4. On satisfiable input, `separationCheck C a b [] = true` returns false. The
   exact supplied-address theorem `not_entails_iff_exists_check` makes the
   empty address an explicit countermodel certificate. If that test is false,
   the code falls through to the complete raw two-branch backend.

The proof at lines 54–76 keeps these cases separate. In particular, a failed
empty-address test is not treated as entailment; it invokes the complete raw
decision. The direct premise shortcut is checked only against the supplied
list `C`, so a query inequality is never smuggled into the premises.

## Expression-level conclusion and Problem 1.7 link

`entailsCheck` at lines 80–82 feeds the exact normalized list and the two exact
query references to `normalizedEntailsCheck`. The final theorem is:

```text
entailsCheck G s t = true iff ExprEntails G s t
```

The proof first applies `normalizedEntailsCheck_correct`, then uses the reverse
direction of `normalize_entails_iff` because the latter is stated as
`ExprEntails iff normalized Entails`. This preserves the inequality direction.

The memo's Problem 1.7 uses finite sets of inequalities and variable queries.
The repository's finite encoding uses lists (where duplicate constraints are
semantically redundant) and permits finite expression queries as a conservative
extension. Variable queries are the `.var` instances. A named-variable parser
or a theorem identifying arbitrary finite-set encodings with a particular
`Fin n` numbering is outside this Lean interface; it is an ordinary finite
encoding convention, not a missing semantic premise in the theorem. The
TreeSemantics type-set correspondence is likewise an inherited C001 boundary,
not a new claim made by this final module.

## Runtime and evidence boundary

The new module's `def` declarations are finite Bool computations over finite
lists, vectors, syntax and the already defined finite backends. A source scan
of the exact module found no `noncomputable`, `opaque`, `axiom`, `sorry`, or
`native_decide`; `classical` occurs only in the proof of
`rawNormalizedEntailsCheck_correct`. This source observation is not a
replacement for the required dependency/runtime axiom audit.

The following remain PENDING for the exact pinned composition revision:

- fresh combined Lean build and whole-library kernel replay;
- declaration dependency and runtime-classical-choice audit for the imported
  composition;
- native full-frontend regressions and source-hash readback;
- combined-tree CI and exact published-main readback;
- any synchronized update to the pending execution record and canonical
  project ledgers.

These are validation and publication gates, not semantic blockers found by
this source review. The theorem itself introduces no witness-length bound,
quantitative closure estimate, regular-model premise, or finite-tree
interpretation.

Status: independent semantic readback COMPLETE at source commit
`9f7d57cbd695a68dd52a69dc81b8446bd7c85d9e`; no source, import, workflow,
shared-record, build, or Lake-tree write scope is retained. The review branch
contains only this new note until its handoff commit.

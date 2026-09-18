# Lean: finite propagation summaries and executable normalized satisfiability (stage 6, second layer)

Date: 2026-09-18. Workstream A018, stage 6 of the C080 candidate (issue #31,
tracker #34, integration #35). Modules: [StackSummary.lean](../lean/Subtail/StackSummary.lean),
[StackReachability.lean](../lean/Subtail/StackReachability.lean),
[CanonicalReachability.lean](../lean/Subtail/CanonicalReachability.lean),
[StackSummaryAudit.lean](../lean/Subtail/StackSummaryAudit.lean).
Authored on `lean/finite-propagation-2026-09-18` (ChatGPT session
`finite-propagation-20260918`, source revision `bfc442d`, checker revision
`76e11d5`); this readback was written by the integrator (Claude, Claude Code
session) because the authoring session paused before committing its announced
note and results file. It is a same-repository readback, not a human referee.

**Status: kernel-checked, standard axioms only. It supplies a TOTAL executable
satisfiability test for finite normalized constraint systems and an exact
countermodel test at a SUPPLIED address. It does NOT decide entailment: the
existence of a separating address remains an explicit unbounded existential.
Nothing here changes the CANDIDATE status of C080.**

## 1. Objects, read back into ordinary mathematics

`System n` is a pushdown-style rule set over the binary alphabet with control
states `Fin n`: `eps p q`, `push a p q` (push letter `a`), `pop a p q` (pop
letter `a`), each a Boolean table. `reverse M` swaps pushes and pops and
reverses every rule; `reverse_reverse` is checked.

`Balanced M p q` is the inductive relation of excursions that never read
below their starting stack (reflexivity, one epsilon step, composition, and
`push a; balanced; pop a`). `balancedCheck` is an executable table with
`balancedCheck_correct : balancedCheck M p q = true ↔ Balanced M p q`. The
table is computed by finite closure, without any stack-height cutoff.

`Step`/`Reaches` are the ordinary one-step and reflexive-transitive
configuration relations on `(control, stack)`. `Pop M p w q` means `w` can be
popped entirely while moving from `p` to `q` through balanced excursions
between the pops; `pop_iff_reaches_empty` identifies it with reaching the
empty stack. `Normal M p u q v` is the minimum-stack factorisation: a common
tail `m` of `u` and `v` survives untouched, the prefix of `u` above it is
popped, then the prefix of `v` above it is pushed (a reversed pop of
`reverse M`). The theorem

    reaches_iff_normal : Reaches M (p,u) (q,v) ↔ Normal M p u q v

is proved by induction on runs (`normal_step` absorbs one step of any kind
into the normal form). `CutNormal` restates it with explicit cut indices
`i ≤ |u|`, `j ≤ |v|`, giving the executable `reachesCheck` with
`reachesCheck_correct : reachesCheck M p u q v = true ↔ Reaches M (p,u) (q,v)`,
and `controlReachCheck_correct : controlReachCheck M p u q = true ↔ ∃ v, Reaches M (p,u) (q,v)`
(reach control `q` with ANY stack, via a path in the finite `controlEdge`
graph, `exists_pop_iff_path`).

`CanonicalReachability.systemOf C` translates the four normalized constraint
forms of the canonical-model layer into rules: `leq p q` is an epsilon rule,
`lower l p q` pushes (`a = 1` at `p → q` from the right factor, `a = 0` from
the left), and the upper-product form pops. The key identification is

    derived_iff_reaches : Derived C S q w ↔ ∃ p u, S p u ∧ Reaches (systemOf C) (p,u) (q,w)

so the inductive propagation closure of the canonical-model layer IS
configuration reachability of `systemOf C` from the seed configurations.
`derivedCheck` and `safeCheck` (no denied variable is reachable with any stack
from any seed) are executable with `derivedCheck_correct` and
`safeCheck_correct : safeCheck C seeds = true ↔ AvoidsDenials C (seedPred seeds)`.
`forcedList`/`pathList` are the finite seed lists for forced roots and for all
prefixes of a supplied address, with `forcedList_pred`/`pathList_pred`
identifying them with the canonical-model seed predicates.

## 2. The two checked endpoints

    satCheck_correct : satCheck C = true ↔ Satisfiable C

is total: `Satisfiable` quantifies over ALL predicate-valued prefix-closed
trees (the canonical-model layer), and the Boolean is a finite computation.

    separationCheck_iff_countermodel :
      separationCheck C a b w = true ↔ ∃ rho, Models C rho ∧ (rho a).nodes w ∧ ¬ (rho b).nodes w

decides, for a SUPPLIED finite address `w`, whether some arbitrary model of `C`
separates `a` from `b` at exactly that address. Finally

    not_entails_iff_exists_check : ¬ Entails C a b ↔ ∃ w, separationCheck C a b w = true

leaves the address existential explicit. No stack bound, derivation-length
bound, or C080 result enters any of these proofs.

## 3. Executed evidence

Local Lean 4.33.1 at the integration head: full `lake build Subtail` with the
seven stage-6 modules added to the aggregator, `leanchecker` replay of
`StackSummaryAudit` and `CanonicalModelAudit`, and `#print axioms` of all 182
stage-6 declarations (seven modules): theorems use at most `propext`,
`Quot.sound`, `Classical.choice`; definitions use no classical choice; no
`axiom`, `opaque` or `sorry`. The authoring session's isolated workflow at
`76e11d5` passed (run 35335523579).

[check_stack_summary.py](../experiments/check_stack_summary.py) `--lean`
(seed `2026091831`) compares the compiled Lean Booleans against an independent
P-automaton predecessor saturation that uses no stack cutoff:

| Count | Value |
|---|---|
| Systems (one- and two-control, mixed / no-push / no-pop) | 68 |
| `reachesCheck` comparisons | 14,256 |
| `controlReachCheck` comparisons | 1,488 |
| `balancedCheck` comparisons | 176 |
| Complete monotone breadth-first cross-checks (no-push or no-pop systems) | 8,050 |
| Constraint systems: `satCheck` / supplied-address `separationCheck` comparisons | 32 / 896 |

Saved: [results/finite-propagation.json](../results/finite-propagation.json)
(`PASS`; the workflow also replays it under a second `PYTHONHASHSEED`). Finite
agreement is a regression of the executable definitions; the all-length
statements are the kernel-checked theorems above.

## 4. Limits and next obligations

* Entailment is not decided: `not_entails_iff_exists_check` still needs a
  bound or a finite representation for the separating address (the Pop/Post
  regularity and finite summary `I_C` of the bridge review, then the
  ordered-cut correspondence, absorption, C029/C031 and the composition with
  the terminal decision). These remain open in #31.
* Input normalization from compound constraints to the four forms is not
  formalized.
* The finite closure tables are deliberately exhaustive and exponential; no
  efficiency claim is made.
* Same-author formalization plus an integrator's readback; no human referee.

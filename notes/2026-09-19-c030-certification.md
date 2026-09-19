# Direct C030 certification

Date: 2026-09-19. Workstreams A011/A013; coordination #37; prior review PR #46.
Session: ChatGPT c030-integration-certification-20260919.
Base: `7185b15140fbc629bf1825063d1652d4feb8a43f`.

## Status at this draft

The written direct proof and independent replay are integrated through PR #46.
This follow-up is an isolated Lean implementation attempt. Compilation and
kernel verification are pending; the source must not yet be cited as a checked
C030 theorem. The theorem target and original definitions are not weakened.

The only source dependency is `Subtail.TreeSemantics`, which imports
`Subtail.Basic`. No forward bridge, canonical-model theorem, pushdown
saturation, decision algorithm or C029 dependency is introduced. Neither
`lean/Subtail.lean` nor another worker's shared proof/CI/ledger path is edited.
The dedicated C030 workflow explicitly builds the new opt-in modules.

## Exact target and ordinary proof

For every `I : Instance k` whose final states have no transitions, construct
`constraints I : List (Constraint (2*k+1))` with indexed variables `a q`, `v q`
and `b`. With no assumptions on Bad, ordered flags, finals or the initial state
beyond terminality, prove both:

- `Satisfiable (constraints I)`;
- for every finite word w, `Witness I w` iff some valuation of arbitrary
  prefix-closed trees models the constraints and has w in a_initial but not
  v_initial.

See [the complete direct review](2026-09-19-c030-independent-review.md) for
both all-word proofs, saturation audit, boundary cases, exact counts, and the
hypothesis-mutation counterexample. This is the existing end-to-end outline,
not a new speculative route or a pile of unrelated local lemmas.

Implementation order:

1. Define the finite normalized list on exactly `Fin (2*k+1)` and prove its
   equivalence to the five displayed clause families (Laws).
2. Prove proper-prefix nonfinality, upper suffix propagation and lower path
   transport. Deduce separation implies every original Witness conjunct.
3. Define R_q as defined paths ending at nonfinal controls; prove prefix
   closure and the bottom-a/R-v baseline model, including infinite trees.
4. Define A_q from prefix/run/suffix decompositions of the candidate word and
   V_q from R_q plus transported ordered flag seeds. Prove prefix closure,
   model satisfaction and exclusion of the query word from V_initial.
5. Derive same-word equivalence and the non-entailment corollary. Audit
   dependencies and named empty/undefined/flag-orientation examples.

Any incomplete implication remains an explicit obligation; no custom axioms,
`sorry`, finite-depth substitution or imported unproved transfer is permitted.

## Validation plan and environment boundary

The local container has no Lean/Lake installation, and direct network DNS was
unavailable. Pinned Lean 4.33.1 compilation is therefore performed by an
isolated read-only GitHub Actions job, not claimed from source inspection.
The exact workflow commit, job outcomes and failed attempts will be recorded
at handoff. Kernel replay and axiom readback are separate steps. The normalized
constructor must have no `Classical.choice` runtime dependency.

The previously published checker was replayed locally in this session: all
200196 query words and 12956 baseline models matched the archived semantic
fields, with 416 positive words. All eight supplied artifact hashes matched.
This replays the same independent checker; it is not a second blind review or
a Lean proof. E021 and the budget differential were not run in this session.

## Scope and integration

PR #46 merged at the base above with its four additive files only. Main's
preexisting C029 contribution was preserved. The PR's six existing workflows
passed; post-merge and new certification results must be reported separately.
The PR #46 integration lease was released in #37. C029 completion has another
active owner and remains outside this task. Shared navigation links were
requested from the serialized ledger owner; no acknowledgment is assumed.

C030 certification is optional for the converse. It is not a prerequisite for
the forward decision procedure and does not establish a complexity equivalence
or the separate budget claims. A successor must read current #37 ownership and
the final handoff before changing the new modules or shared imports.

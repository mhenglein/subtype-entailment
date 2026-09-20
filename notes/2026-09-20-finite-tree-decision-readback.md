# Unconditional finite-tree decision: proof and validation

Date: 2026-09-20. Actor: finite-decision-20260920. C085, E057, A010/A018.
Base: `52e790fb7360ec676ca76f5a391c9a35375a912b`.
Checked source: `4159c58` on `codex/finite-decision-20260920`.
Coordination: [#58](https://github.com/mhenglein/subtail/issues/58),
integrator lease in [#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5747764108).

## Exact result

The optional `FiniteTreeDecision` module defines a total executable Boolean
for every finite list of bottom/product expression inequalities and query:

```lean
theorem entailsCheck_correct (G : Input n) (s t : Expr n) :
  entailsCheck G s t = true ↔ FiniteExprEntails G s t
```

`FiniteExprEntails` uses the unchanged semantics: every valuation whose
variable trees have bounded product-address lengths and satisfy G also satisfies
s <= t. All constructors are bottom and one covariant binary product. There
is no supplied bound, satisfiability, regularity or classifier hypothesis.
The definition computes; it does not use a classical `Decidable` instance.
The previous [ordinary argument](2026-09-20-finite-tree-reduction.md) and
[semantic module readback](2026-09-20-finite-tree-readback.md) retain their
original scope. This result completes their executable-classifier obligation.

## Critical argument and declaration map

The graph has n controls. Its epsilon edges are balanced excursions in the
reversed pushdown system; its letter edges are reverse pops. With initial
control q and accepting control m it recognizes exactly Pop(reverse M,q,w,m).
The already checked cache supplies graph reachability. `growthCheck` enumerates
all pairs p,r and both letters, testing an original push r-a->p and a graph
return r->p. It is a finite computation, using the existing terminating
saturation and reachability routines.

| Ordinary implication | Checked declaration |
| --- | --- |
| Cached Boolean is true iff a letter edge p->r has a reverse-Pop return word r->p | `FiniteTreeDecision.growthCheck_correct` |
| A negative result excludes every nonempty reverse-Pop self-loop | `FiniteTreeDecision.growthCheck_false_no_loop` |
| Without a nonempty self-loop, every consumed word has length < n | `PopAcyclic.pop_length_lt_of_no_nonempty_loop` |
| Negative growth supplies the semantic theorem's uniform bound | `FiniteTreeDecision.growthCheck_false_bound` |
| In a normalized constraint system, the original push target is forced | `FiniteTreeDecision.push_target_forced` |
| Positive growth excludes all finite normalized models | `FiniteTreeDecision.growthCheck_true_noFiniteModel` |
| The same flag excludes finite valuations of the original expressions | `FiniteTreeDecision.run_growth_noFiniteExprModel` |
| Growth OR the existing arbitrary entailment Boolean decides finite entailment | `FiniteTreeDecision.entailsCheck_correct` |

The negative-loop argument must handle balanced motion before the first letter.
Decompose a putative loop into Balanced(p,r), the pop r-a->s, and Pop(s,w,p).
Postcompose its tail with Balanced(p,r), obtaining Pop(s,w,r). The enumerated
edge r-a->s now has the required return, contradicting a negative classifier.
No assumption that the first consumed edge starts at p is made.

The length argument counts consumed letters rather than internal transitions
of balanced excursions. A structural trace contains |w|+1 boundary controls
and a consumed prefix witnessing reachability to each. Induction proves the
tail controls distinct. If its new initial control occurred again in the tail,
the corresponding prefix would be a nonempty Pop self-loop. Thus the trace
is duplicate-free and has length at most n. Empty words and epsilon cycles
are allowed; n=0 has no control and the quantified claim is vacuous.

For a positive test, the selected reverse pop reverses a lower-product push.
Its source is therefore a forced product root, and appending its return word
gives the existing finite-model obstruction. For a negative test, the proved
length bound supplies `finiteEntails_iff_entails_of_uniform_reverse_pop`.
The existing finite/arbitrary normalization equivalences then connect both
branches to the original expressions. No old theorem or semantic definition
was changed, and no new default import was added.

## Independent review

The isolated helper author contributed `66f2032`, incorporated as `8cd2a63`.
The parent developed the classifier/composition independently of that helper's
implementation, using the agreed exact signature. A separate read-only reviewer
checked the supplied argument, definitions, edge orientation, positive and
negative branches, trace proof, zero-control case and normalization composition.
This is source-based adversarial review, not a claim of blind rediscovery or
human peer review.

- [Mathematical/source readback](https://github.com/mhenglein/subtail/issues/58#issuecomment-5747824420).
- [Final checker/CLI/workflow review](https://github.com/mhenglein/subtail/issues/58#issuecomment-5747841570).

The reviewer found the old semantic audit did not cover the new modules and
still described the classifier as ordinary Python. The new dedicated checker
and receipt close that coverage gap; the old checker's live scope text was
corrected. The first local development receipt named the earlier HEAD while
the source was uncommitted. It is not used as commit-pinned evidence. The
fresh wb-marcus receipt below names `4159c58` and hashes the actual sources.
The final reviewed proof blob is `bbf310947d508fb2d01cb91976f3482fcc7548a6`.

## Reproduction and results

In an isolated wb-marcus checkout at `4159c58`, pinned Lean 4.33.1:

```sh
python3 scripts/check_finite_tree_decision.py --output tmp/finite-tree-decision.json
python3 scripts/check_finite_tree_reduction.py --output tmp/finite-tree-semantic-recheck.json
python3 scripts/check_lean.py
```

All three commands PASS. The [combined receipt](../results/finite-tree-decision.json)
preserves exact revision, source hashes, host and runtime outputs:

- New modules: build and kernel replay; all 13 declaration closures, including
  private `pop_trace`; all three executable definitions have no classical-choice
  dependency. Closure checks include imported runtime dependencies.
- Native classifier: 308 comparisons with the independent predecessor oracle,
  seed 5807, including eight named boundary cases. All agree.
- Actual CLI: nine cases pass. These cover growth vacuity, cold unsatisfiability,
  finite negative inputs, finite/arbitrary disagreement, infinite graph rejection,
  UNKNOWN under a cap, zero variables and query-only product syntax. Three
  negative cases also compile C084 instance certificates through the kernel.
- Existing semantic layer: 31 declaration closures, 46 Python tests and the
  original E056 comparisons/census pass, plus its seven CLI checks.
- Default Lean core: `scripts/check_lean.py` passes separately on the same tree.

The CI workflow invokes the new checker and includes its path in both trigger
filters. Main publication and CI status are recorded in #58/#37; local or remote
PASS is not a claim that a future GitHub run has finished. Old evidence remains
at its original revisions. The new source/checker files are unchanged by the
later documentation-only integration commit.

## Boundaries and next question

The CLI uses the checked finite Boolean and the same run's growth flag. Missing,
duplicate or contradictory native markers return UNKNOWN. Failed or capped
processes cannot supply a decision. Python growth classification remains only
an independent diagnostic; it cannot bypass Lean with a positive answer.

JSON parsing, source emission, native execution and graph extraction/finiteness
remain external to the theorem. C084 instance certificates prove arbitrary
non-entailment of emitted expressions; Python checks that their variable roots
unfold to finite trees. This work does not add a separate finite-SAT Boolean
theorem, change C081/C084, improve E055 performance, settle C080 F, or establish
any explicit-top or novelty claim. The seed-dependent height bound is not a
new global shortest-witness estimate.

The next paper revision can now include the finite-tree consequence and this
short finite-control argument, with an exact comparison to earlier finite-tree
results. Profiling the remaining deep decision timeouts is a separate useful
task. Neither task is assigned by this handoff.

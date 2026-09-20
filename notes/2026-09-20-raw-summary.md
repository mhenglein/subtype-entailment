# Exact cached construction of the raw summary automaton

Date: 2026-09-20. Actor: raw-summary-20260920. A010/A018, C081, issue #62,
coordinated in #37. Base: `5adaa2949ffaeab94c4b7687d12b8ca6bd84ee94`.
Status: implemented with checked whole-Instance and endpoint equality.
Final validation, revisions and remaining limits are in the
[readback](2026-09-20-raw-summary-readback.md). The initial route and failed
attempts below are preserved.

## Exact target

For every finite normalized bottom/product constraint list `C` and controls
`a,b : Fin n`, build exactly `SummaryAutomaton.summaryInstance C a b` using
the existing proved balanced and control-reachability matrices. Equality must
hold on every physical state, including unreachable states, and every ordered
flag pair. The final raw Boolean must equal the current E059 raw Boolean with
no caller hypothesis. Tree semantics remain arbitrary prefix-closed sets.

This is a runtime refinement of C081. It does not change the decision theorem,
its witness bounds, or the set of signatures to which it applies.

## Objects and construction

The physical states remain `states n`, the same ordered enumeration of pairs
`(B,A)` of subsets of `Fin n`. The alphabet is the two Booleans. Initial state
is the encoding of the forward empty-word pop set from `a` and the reversed
empty-word pop set from `b`. Each letter advances both subsets by the same
pop edge followed by a balanced excursion. Transitions remain total.

Let `M` be a finite push/pop/epsilon system and let `cache : Cache M` contain
forward and backward balanced matrices and the backward control-path matrix.
The constructor accepts these data without treating an arbitrary cache as
correct. Its equality theorem requires `M = systemOf C` and `Correct M cache`.

The initial subsets are ordered filters of `finRange n` using the appropriate
matrix row. The successor subsets use the existing cached `nextSet`. Thus all
subsets belong to the original powerset enumeration, independently of cache
correctness. The original `encode` and `decode` define their physical indices.

For a control `m`, cached danger means that some denied control `d` has a true
`cache.paths[d,m]` entry. Cached satisfiability checks that no forced root can
reach a denial, using the existing cached `controlReachCheck`. Compute these
fixed values once. A state's Bad bit is the original disjunction of global
unsatisfiability and a dangerous member of its forward subset. The final bit
and all ordered/diagonal flags retain the original formulas.

There are finitely many controls, subsets and pairs. Existing terminating
saturation and finite graph searches compute the matrices. All construction
loops are finite; no abstract choice, state quotient or reachability-only
replacement is proposed.

## Ordinary equality argument before implementation

1. `CanonicalReachabilityFast.Correct` equates each forward/backward matrix
   entry to the reference `balancedCheck`, and each path entry to the reference
   backward `pathCheck`. `prepare_correct` supplies this invariant.
2. The empty-word pop test is the balanced test. Replacing each filter predicate
   by an equal Boolean preserves the whole ordered initial subset lists.
3. `CanonicalReachabilityFast.nextSet_eq` gives exact successor-list equality
   for every input subset and both letters. The original encoding then gives
   the same initial index and every transition index, not just the same sets.
4. Substituting the path-matrix equality gives the original `dangerCheck`.
   `controlReachCheck_eq` gives the original forced-root satisfiability check.
   Therefore every Bad bit is equal. Final bits and flags are unchanged.
5. Componentwise equality gives equality of the entire finite `Instance`.
   Applying the unchanged E059 infinite and terminal decisions preserves the
   exact raw Boolean. This step imports C081; it does not reprove completeness.
6. The existing `EntailmentPrepared.prepare_eq` identifies its materialized
   System/cache record with the reference prepared record. The raw wrapper
   prepares once; the frontend fallback reuses its already prepared record.
   Substituting steps 1–5 proves both unconditional endpoint equalities.

The semantic risks to check in Lean and independent review are ordered subset
encoding, reverse-system orientation, handling of zero controls,
unreachable states, global UNSAT and ordered/diagonal flags. A change preserving
only accepted words would suffice semantically, but exact Instance equality is
the simpler available argument and permits direct component comparisons.

## Falsification and measurement

E059's fixed seven raw probes and four-variable empty instance distinguish
this change from frontend shortcuts. Keep the original `#eval` invocation,
20-second wall/CPU cap, Linux 16-GiB address-space cap and one Lean thread.
Separate diagnostic `--run` traces from matched timings. Test empty, denial,
epsilon, lower, upper, reverse-oriented and mixed constraints, including all
physical states/flags on tractable small inputs. Preserve expected answers
from independent semantic fixtures; agreement alone is not an oracle.

Measure larger raw inputs separately. After eliminating exhaustive balanced
enumeration, the `4^n` physical-state enumeration, dense flag matrix, encoding
search or the unchanged infinite/terminal decision may become the next cost.
No universal speedup or peak-memory improvement follows from a passing suite.

## Initial review and next decision

The existing E059 trace places the four-variable timeout in summary
construction. The present source inspection identifies reference balanced
enumeration there; the new algorithm's native cost remains unmeasured.
Independent source review is assigned with read-only scope. Formal equality,
kernel/runtime audit and matched native runs remain pending.

This refinement neither supports nor refutes decidability for explicit top or
other constructors. Failure would identify an implementation bottleneck in the
already decided fragment, not an undecidability obstruction. Next implement
the exact constructor and test the measured four-variable boundary.

## First ablation: relation tables alone

At `3d7ee86`, pinned build/kernel, 45 declaration closures (22 executable)
checks and all five actual CLI cases pass. The cached relation constructor
still times out in `summary` on the four-variable empty input. This is a
negative performance result, not a failed equality proof. Preserve its full
receipt before testing another change.

The remaining constructor repeatedly evaluates `decode` inside every entry of
its dense flag matrix. `decode` regenerates the powerset-pair list before an
indexed list lookup. The next ablation will tabulate those physical-state
pairs once and reuse their lookups. The finite table has the same order and
its entry at `q` is exactly `decode q`; replacing these occurrences therefore
preserves the existing whole-Instance equality. This does not reduce the
physical state count or flag-matrix size. Performance remains to be measured.

## Second ablation: reuse decoded physical states

At `2233aea`, the ordered physical-state vector is shared by every Bad, final
and flag lookup. `stateTable_get` proves its lookup equals the original
`decode`; the whole-Instance theorem substitutes that equality. The original
transition encoding remains unchanged. Kernel replay, runtime dependency
checks and actual CLI checks pass. Diagnostic empty-constraint probes at
three, four and five variables complete; six variables remain UNKNOWN in
construction. This does not change the exponential state or dense flag counts.

The first proof draft at `c74323b` left a definitional index-cast equality.
Adding `rfl` after simplification fixed elaboration without changing the
statement or runtime construction. This is a proof-script repair, not an
additional mathematical assumption.

## Validation batching correction

The independently authored harness at `82b3e68` placed all queries for a
constraint case in one process. Its 26 one/two-variable cases passed; each
three-variable case timed out while testing nine candidate/reference pairs.
These results remain UNKNOWN in the receipt.

At `5047afa`, each query pair receives its own unchanged 20-second process
cap. All 29 cases, 83 queries, physical fields and fixture identities remain.
This increases the total allowed validation time per constraint case. It is
not a speedup measurement; raw benchmarks retain one query per process and
their original caps. Final acceptance requires every pair to complete, with
both exact Lean instances checked against the independent Python oracle.

This first repair was insufficient: a candidate/reference pair prints over
9,000 bytes, while the existing runner keeps an 8,000-byte tail. Independent
review identified the dropped first marker. At `66f545e`, one variant and one
query run in each process; the largest fixed marker is 4,611 bytes. The full
corpus still has 83 pairs, now emitted by 166 processes.

That repaired capture completes 157 processes under 20 seconds. The nine
remaining reference runs for the n=3 contradiction case time out; all 83
candidate runs complete. These are UNKNOWN reference comparisons, not failed
candidate answers. The final correctness-only run and CI use 60 seconds per
process to validate the slow original constructor. Raw performance measurements
keep their original 20-second cap. The readback records the actual acceptance
results and preserves every earlier receipt.

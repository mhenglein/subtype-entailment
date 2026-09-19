# C081 performance plan: defer terminal query expansion

Date / author: 2026-09-20, `c081-performance-review-20260920`.
Approach: [A018](../research/approaches/A018.md). Claims and experiments:
[C081](../research/claims.md#c081), [E052](../experiments/README.md#e052).
Base: `c946d86b9e65da2877e0df42c710abbdcb5a4037` on the isolated branch
`codex/c081-complexity-20260919`, worktree
`/Users/marcushenglein/Documents/ChatGPT/Subtail-c081-complexity`.
Owned path: this new note only. No Lean source, experiment result, ledger,
workflow, or shared-state file was changed.

## Question and current boundary

The qualitative C081 theorem is already checked, but E052 shows poor native
performance: 25 of 38 cases completed and agreed, while 13 timed out at the
20-second cap. A timeout is `UNKNOWN`, not a negative answer. The direct raw
positive probes did not finish.

This review asks one narrower question: which construction dominates a small
raw `UNKNOWN` case, and what one semantics-preserving change can remove avoidable
work without changing the arbitrary-tree theorem?

I selected `raw-reflexive`, the smallest direct raw case:

```text
C = [], n = 1, query = 0 <= 0, expected answer = true
```

The saved E052 row is `UNKNOWN` at 20.159 seconds. It calls
`rawNormalizedEntailsCheck` directly, so normalization and the expression
frontend do not hide the backend cost.

## Readback of the current constructions

For normalized constraints `C` and variables `a,b`,
`rawNormalizedEntailsCheck` constructs one
`SummaryAutomaton.summaryInstance C a b` and returns

```text
!(infiniteWitnessCheck I || terminalWitnessCheck (terminalize I))
```

`summaryInstance` has `states n` equal to every pair of subsets of
`Fin n`. Its transitions call `advance`, then `nextSet`. `nextSet` scans
possible predecessor and successor controls and calls `balancedCheck` for the
balanced middle segment.

`StackSummary.balancedCheck` is an exact but deliberately exhaustive table
check:

```text
(subsets (pairs n)).all (fun R =>
  if closedCheck M R then (p,q) ∈ R else true)
```

There are `n^2` possible pairs, so `subsets (pairs n)` has `2^(n^2)` list
entries. `closedCheck` then checks identity, epsilon, transitivity, and both
push/pop wrap cases. The existing theorem
`balancedCheck_correct` makes this a valid reference implementation; this task
does not replace it.

The terminal branch is defined in `RankQueryDecision.terminalWitnessCheck`.
It first checks the empty word, then binds

```text
phi := promote (preimage I RankQueryCoverage.budget)
                     (finishQuery I) (k - 2)
```

before scanning the finite set of one-letter references. Each reference is
checked by `safeReferenceCheck`; only a safe reference needs
`satCheck (prefixGraph I B) phi`. The source places the large `phi` binding
outside that safe-reference test.

## Reproducible profiling

The workbench was `wb-marcus`, checkout
`/home/marcus/workspaces/subtail-worktrees/entailment-completion-20260919` at
`a7c4fbc0fd84c1ad64167e2927e47dc86172937a`. It was clean and its relevant
Lean source hashes matched the local C081 source. The workbench had Lean
4.33.1 and Lake 5.0.0. The E052 harness itself is pinned locally at
`e867092e32e368eac34065b97cc6871f3b60bc73`; the workbench checkout contains
only the compiled Lean project, so all probes were temporary files under
`/tmp`.

Each probe ran in a new process group with `LEAN_NUM_THREADS=2`, a 120-second
CPU limit, a 16 GiB address-space limit, and a shorter 30-second wall limit
for these small probes. A timeout or out-of-memory termination is recorded as
`UNKNOWN`; it is never treated as a Boolean answer. Linux `ru_maxrss` below
is in KiB.

| Probe | Result | Wall time | Peak RSS | Interpretation |
| --- | --- | ---: | ---: | --- |
| `infiniteWitnessCheck I` for `raw-reflexive` | `false` | 0.922 s | 826,032 KiB | The C029/infinite branch finishes on this instance. |
| First `safeReferenceCheck` in the terminal loop | `false` | 0.655 s | 829,964 KiB | The candidate gate is cheap and rejects this reference. |
| Existing `terminalWitnessCheck (terminalize I)` | no result; Lean internal OOM | 12.527 s | 3,099,876 KiB | The terminal path is the failing branch. |
| `Q.length` for the eager `promote (preimage ...) ...` | no result; Lean internal OOM | 12.415 s | 3,106,772 KiB | Query materialization itself does not finish. |
| One fixed `satCheck (prefixGraph I B) Q` | no result; Lean internal OOM | 13.847 s | 3,102,064 KiB | The SAT call is also infeasible when reached. |
| Same terminal loop with `phi` created only after a safe gate | `false` | 0.692 s | 835,636 KiB | The full raw-reflexive terminal scan completes without building `phi`. |

The last row is a temporary probe, not a source change or a correctness result.
It uses the same definitions and replaces

```text
safeReferenceCheck I B && satCheck (prefixGraph I B) phi
```

with the truth-table equivalent short-circuit form

```text
if safeReferenceCheck I B then
  satCheck (prefixGraph I B)
    (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2))
else false
```

The difference is operational: in the current definition, entering the `let`
forces the large query before the Boolean `&&` can reject every reference.

As a separate small scaling check, direct all-false `balancedCheck` systems ran
at wall times 0.652 s, 0.648 s, 0.707 s, and 1.405 s for `n=1,2,3,4`
respectively (the first roughly 0.6 s is Lean process/import overhead). This
confirms the documented `2^(n^2)` table enumeration, but it was not the
measured bottleneck in the selected `n=1` raw case. `summaryInstance` and its
transition table also completed in the small probe; the terminal query
materialization dominated the observed failure.

## Proposed exact optimization

Introduce a private candidate helper, or rewrite the terminal loop, so the
expensive promoted query is constructed only after `safeReferenceCheck` is
true:

```lean
if safeReferenceCheck I (oneLetter a f p) then
  satCheck (prefixGraph I (oneLetter a f p))
    (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2))
else false
```

Keep the empty-word check first and preserve the same finite enumeration of
`a`, `f`, and `p`. This is exact because all definitions are pure and Boolean
`if`/`&&` have the same truth table. The proof interface is a local lemma for
one candidate:

```lean
(if safeReferenceCheck I B then
    satCheck (prefixGraph I B)
      (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2))
  else false)
=
  safeReferenceCheck I B &&
    satCheck (prefixGraph I B)
      (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2))
```

A two-case proof on `safeReferenceCheck I B` establishes this lemma. List
`any` congruence then gives equality with the current
`terminalWitnessCheck`; the existing
`terminalWitnessCheck_spec` and `terminalWitnessCheck_sound` proofs can be
reused. No semantic argument about trees, terminality, or the C080 coverage
claim is needed.

Let `k` be the number of summary states, `R = 2 k^2` the one-letter reference
count, and `E(k)` the cost of materializing the promoted query. The current
code pays `E(k)` before checking any reference. The lazy form pays only the
cheap safe-reference tests until the first safe candidate, then pays `E(k)`
once. When all candidates are unsafe, as in the measured raw-reflexive case,
the cost changes from `E(k) + O(R)` to `O(R)`; the observed bounded probe
changed from OOM to 0.692 seconds. The worst-case asymptotic cost remains
unchanged when a safe candidate exists, and the later graph SAT call can still
be expensive. This is therefore a targeted practical improvement, not a
complete complexity bound or a claim that all 13 E052 cases will finish.

## Acceptance, limits, and next experiment

Accept the implementation only if the local equality lemma compiles, the
existing terminal correctness theorem still replays, and the direct raw
regressions preserve their independent answers. Re-run the E052 diagnostic
with the same 20-second per-fixture cap; retain `UNKNOWN` for any remaining
timeouts. Also run the existing terminal and C029 suites. No timeout should be
converted to `NO`.

The next useful measurement is the same lazy probe on the remaining raw and
frontend cases that reach terminalization. If some candidate passes the safe
gate, measure the separate cost of `preimage` materialization and the graph
SAT call; this will decide whether query DAG sharing or a lazy query iterator
is the next optimization. The current evidence does not justify claiming
that those larger constructions are solved.

## Independent and adversarial checks

I inspected the exact definitions of `balancedCheck`, `summaryInstance`,
`normalizedEntailsCheck`, `rawNormalizedEntailsCheck`, `entailsCheck`,
`terminalWitnessCheck`, the E052 harness, and the relevant imported RankQuery
runtime definitions. All source hashes used by the workbench probes matched
this checkout; no source or compiled artifact was changed there.

The proposed rewrite preserves candidate ordering, `safeReferenceCheck`,
`prefixGraph`, `preimage`, `promote`, `satCheck`, and the final Boolean
combination. It changes evaluation order only. It does not prove that query
materialization terminates within a useful bound, and it does not improve the
exponential `balancedCheck` table enumeration. A bounded probe cannot prove
universal runtime behavior.

No new Lean formalization was needed for this review. The disputed point is
operational evaluation order, and the one-case equality is the appropriate
small proof obligation if the optimization is implemented. The existing C081
proof and arbitrary-tree semantics remain the authority.

## Handoff

Result: the selected direct raw `UNKNOWN` case is dominated by eager promoted
terminal-query construction. A safe-gated construction is an exact,
semantics-preserving optimization with a measured 0.692-second temporary
probe, while the existing code reaches an internal OOM after 12.527 seconds.

Evidence remains bounded and local to Lean 4.33.1 on the checked `wb-marcus`
source pin. The optimization is proposed only; no implementation or Lean
source was changed in this task. The write scope is this note only and is
released with the pushed commit. Parent integration should inspect the patch,
recheck the exact main/source pins, and rerun the listed regressions before
adopting it.

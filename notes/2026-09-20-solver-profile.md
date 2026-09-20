# Deeper solver profiling and optimization route

Date/session: 2026-09-20, solver-profile-20260920. A010/A018, C081/C085;
E055 follow-up, #60 under #37. Base `3ce866e`.

## Exact target and route

Improve execution of the existing exact arbitrary-tree entailment decision,
without changing its semantics, termination theorem or UNKNOWN boundary.
First measure the E055 supplied-path depth-twelve case and original-expression
depth-six/eight cases, with smaller controls. Work forwards from the existing
checked `EntailmentFast` and backwards from the phase that exceeds its cap.
No new mathematical assumption, witness bound, complete shortcut or new
constructor signature is part of this attempt.

The profile follows the actual finite-test order: normalization, candidate
paths, positive closure, forward/reverse balanced tables, reverse control
reachability, satisfiability, candidate separation and complete fallback when
needed. Each phase forces and prints a small result before ending its timer.
Diagnostic overhead is included. Its timer is not a substitute for a matched
uninstrumented comparison. Partial trace output is retained on interruption;
a completed marker in a killed process cannot become an accepted answer.

Use the existing wb-marcus environment and an isolated checkout, with the
same 20-second wall/CPU, 16-GiB address-space, one-thread and 32768-KiB stack
limits. GNU time may report peak RSS on completed processes; a missing report
after a group kill remains unknown. Preserve original E055 receipts unchanged.

## Acceptance and proof gate

Choose an optimization only after locating a measured cost. Write its exact
interface, ordinary correctness/equality argument and outstanding obligations
before substantial Lean work. Prefer an additive representation change with
an unconditional equality theorem to the existing decision. Maintain reference
semantics and paper source pins. A failed trial is retained as a failed trial.

The independent source reviewer has no file write scope. Final validation must
include source readback, pinned Lean build/kernel/runtime audits for changed
proofs, independent literal/oracle regressions, and matched end-to-end timing
on the original corpus plus deeper families. A timeout remains UNKNOWN. An
optimization failure does not reopen undecidability for this already decided
fragment; explicit-top and other signatures retain their separate questions.

Results, final interfaces, measurements and handoff follow after execution.

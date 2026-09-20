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

## Measured obstruction and sufficient proof

The first `#eval` trace at `7e03916` lost partial output on interruption.
This is a diagnostic limitation, not evidence that no phase ran. At `d712a40`,
`lean --run` retained the interrupted phases. Supplied depth twelve spent
13.536 seconds in forward saturation and then timed out in reverse saturation.
Both deeper expression cases timed out in forward saturation.

An ablation at the same revision materialized the five primitive transition
matrices for preparation only. Supplied depth twelve finished in 4.178 seconds;
expression depth four fell from 12.651 to 2.877 seconds. Depths six and eight
then timed out in candidate separation, which still used the original list
predicates. These are diagnostic times, not matched production benchmarks.

The selected construction caches each primitive Boolean function
`e : Fin n → Fin n → Bool` as the finite matrix `T[p,q] = e(p,q)`.
There are five such matrices: epsilon, the two pushes and the two pops.
Their construction terminates after exactly five finite square tabulations;
`n = 0` is allowed. Lookup equals the original predicate at every pair.
Case analysis on the two letters, followed by function extensionality, proves
that the resulting `System` equals its input, not merely that it has the same
accepted paths. This equality is unconditional for any finite `System`.

A prepared record stores that system and the existing exact summary cache.
Substituting the equality proves that the whole record equals the reference
record made from the original system. Saturation and all generic path tests
are reused unchanged. The supplied-path test uses the same forced seeds,
denials, source prefixes and target address. Therefore its Boolean answer is
equal by substitution. The same reasoning applies to satisfiability and the
ordered candidate scan. Positive reasoning and the complete terminal fallback
are unchanged. Substitution gives equality of normalized and original-expression
decisions, including empty candidate lists and all arbitrary-tree inputs.

This argument does not claim that the candidate paths are complete or that a
timeout is a negative answer. It changes no witness bound or complexity theorem.
It does not optimize the separate finite-tree endpoint in this attempt.
The opposing research question for explicit top is unaffected: this finite
representation change supplies no new semantic reduction for competing labels.

The additive implementation is `EntailmentPrepared`. The remaining gates are
Lean equality/kernel/runtime checks, independent source readback, oracle
regressions and a matched uninstrumented comparison. The profiler's protocol
and metadata review is also being resolved before final receipts are accepted.

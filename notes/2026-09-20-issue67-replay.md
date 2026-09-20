# Issue 67: full-checkout replay and acceptance boundary

Actor: `publication-sequence-20260920`, parent integrator. Related A017/A018,
E061 and [#67](https://github.com/mhenglein/subtail/issues/67).
The author explicitly released the four new paths at
`da74a4327579ac090846e142f7a1fb834451a7bb`; the
[review/replay claim](https://github.com/mhenglein/subtail/issues/67#issuecomment-5750510396)
precedes this work. Existing compiler and Lean interfaces remain unchanged.

## Result and reproduction

**Partial validation contribution.** Strict execution passes 13/13 cases,
repeated under Python hash seeds 2026092067 and 77. All six capped diagnostic
cases remain UNKNOWN. This does not close #67 or establish an automatic native
depth-two terminal decision. The exact commands are in [E061](../experiments/README.md#e061)
and the [full receipt](../results/issue67-independent/full-checkout-replay.json).

Execution used a new full Git clone, checked out at the exact released head,
on Linux AArch64 with Python 3.13.14. Initial and final Git states were clean.
No source file was patched for execution. Five production Git blob pins,
the harness hash and fixture hash were checked. Strict per-child limits were
60 seconds wall, 55 CPU seconds and 1024 MiB address space. Stress used
20 seconds wall, 18 CPU seconds, 1024 MiB and 100,000 work units. Outputs used
an isolated ignored directory. No Lean process or shared build was started.

The strict pass took 17.460 seconds including parent orchestration; child wall
time totaled 15.935 seconds. Seed-77 replay took 15.661 seconds and stress
23.459 seconds. Every strict child's recorded lifetime peak RSS was 27,068 KiB.
These instrumented diagnostics are not matched performance benchmarks.
Actual per-case wall/user/system CPU and RSS remain in the receipt.

Both within-host strict logical records match exactly after excluding commands,
resource measurements, parent time and hash seed. Shared author-record semantic
answers, union counts and returned-query depth records also match. Five
`finish_queries` call/resumption event counters differ across the author's
Python 3.13.5/x86_64 environment and this Python 3.13.14/AArch64 environment:
three counts are 1 versus 2 and two are 6 versus 7. The exact differences are
retained. They do not change a semantic answer or compiler depth; no byte-identical
cross-host trace is claimed. Extra literal oracle/certificate detail omitted
from the compact author record is included in the new full receipts.

The original four files and their prior failed/capped attempts are preserved.
Private worker/interpreter paths are normalized in the public receipt; hashes
of the unmodified local receipts preserve the exact execution provenance.

## Independent review

The separate `publication_proof_review` agent accepted the contribution at
its exact restricted scope, finding no substantive bug in the S-only projection,
literal oracle, complete DAG enumeration or evidence boundaries.
[Full review with exact source lines](https://github.com/mhenglein/subtail/issues/67#issuecomment-5750568599).
The reviewer read the supplied argument, harness and pinned production definitions;
this was independent review, not blind rediscovery. It edited nothing and ran no
builds. Parent execution is separate evidence. The full readback is preserved
in the new receipt.

For clarity, the two automatic runs reached the cap after 5,784 depth-one clauses
without observing a depth-two success; status remains UNKNOWN. The original
author note and receipt are preserved unchanged. Their pending independent
review and partial-checkout statements describe the author's checkpoint;
this separate record discharges only the stated review and full-checkout
Python replay. Native Lean, frontend and automatic depth-two remain open.

## Remaining obligations and next question

The finite oracle and S-only satisfiable-shape projection are exact only within
the stated scope. The production unpruned iterator and automatic terminal
queries did not complete under the diagnostic cap. Native Lean and the original
finite-expression C081 frontend are NOT RUN for this new family. The observed
depth-two chain is selected by its certificate, not discovered by automatic
whole-decision search. Earlier general Lean results keep their existing evidence;
this contribution changes neither their statements nor their implementation.

The next discriminating target is a successful automatically discovered
native depth-two query, followed by original-expression frontend coverage,
with explicit returned-query provenance and unchanged UNKNOWN semantics.
Any necessary shared instrumentation requires a new exact path/interface claim.
The author's source scope is released; the parent's review/integration scope
releases at the final #37/#67 publication readback, not at a queued workflow.

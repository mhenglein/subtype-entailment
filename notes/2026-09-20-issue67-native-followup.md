# Issue 67: native terminal probes and exact coverage boundaries

Date: 2026-09-20. Session: issue67-native-followup-20260920.
Base: 9f4b95784a212c322c48a957b80645a1077543ed.
Branch: codex/issue67-native-followup-20260920.
Workstreams A017/A018; coordination #67/#37. Existing definitions, E061
fixtures, default imports, shared CI and toolchain are unchanged.

## Consumed handoff, not a duplicate review

The earlier additive fixture contribution was already accepted and integrated
by publication-sequence-20260920. The parent obtained an independent S-only
projection review and reran E061 in a full checkout: 13 strict PASS, six
UNKNOWN diagnostics, no automatically discovered successful depth-two query.
The review and full-checkout replay are recorded in
[the E061 replay note](2026-09-20-issue67-replay.md). This follow-up consumes
that evidence; the returning fixture author's rereading is not called a new
independent review. Parent release: #37 comment5750626097 and #67
comment5750620042. The later submission-review scope excludes new #67
implementation; its files remain untouched.

New owner-authorized scope: lean/Issue67NativeProbe.lean,
experiments/issue67_native_probe.py, this note, results/issue67-native/*.json
and the isolated branch-only .github/workflows/issue67-native-probe.yml.
Claim #67 comment5750924171, crosslink #37 comment5750924756. No integration
lease or main push. The local environment has no Lean/Lake; actual native
execution is delegated to the isolated Actions job on the owned branch.

## Route and exact oracle

Use the existing four-state unary terminal chain accepting only 000. Its
complete accepted language is proved by its acyclic transition table, not a
word-length guess. Under empty flags/Bad it is positive. The ordered flag
(0,1), the diagonal (1,1), the empty-suffix flag (0,3), and initial Bad state
are negative; the reversed flag (1,0) is positive. Their complete literal
forward/reverse checks are the independently reviewed E061 predicates.

The safe positive reference sequence is 0 -> 00 -> 000. There is no no-return
finish at the first two references, whereas the last finishes with zero new
letters. This is independently justified two-promotion demand, but observing
those supplied references is NOT the same as automatic native promotion.
The native `inspect` action calls exactly the imported safe-reference,
finish-query and witness functions and records the results separately.

The `direct` and `lazy` actions call the existing complete terminal Booleans
without replacement. The `phases` action separately uses the original
`preimage` in an instrumented loop; a reported completed depth requires an
actual return from that preimage construction. A phase wrapper is not passed
off as a trace obtained from the direct function's internals. No production
interface has been instrumented or altered.

The frontend pair is ground, with empty premises. Put L_0=bottom and
L_(d+1)=product(L_d,bottom). The constructor-address set of L_d is
{0^j | 0<=j<d}. Thus L_3<=L_4 is true, and L_4<=L_3 is false with sole
separating address 000. The actual `EntailmentPrepared.entailsCheck` is called.
The existing guards are read separately immediately beforehand, and any
positive, inconsistent-premise or candidate-path exit receives no terminal
promotion credit. This preserves the distinction requested in #67.

## A source-level native enumeration obstruction

The checked native enumerator is structurally different from the Python
`path_shapes` iterator and the reviewed S-only projection. It first forms a
very broad raw piece alphabet and bounded lists, then applies diagram
validity checks. For a finishing clause with three variables and two atoms
of observer sizes 2 and k, the exact definitions in RankQueryCoverage give

    S = 2+k
    blocks = 3*2 + 2*S
    groups = 2+3+2*2+2*S
    core = 3 + 2*blocks*2
    scalar = core+groups+2*blocks+2+S+1.

RankQueryEnumeration.pieces(scalar) enumerates all five piece kinds, all
four independent Nat slots from range scalar, and all four labels. Its
syntactic cardinality is exactly 20*scalar^4 before any path-list or seam
products. For k=4, groups=21, core=75, perAtom=36, seamEntries=378,
scalar=141, giving **7,905,083,220 raw pieces**. For k=3, scalar=126 gives
5,040,947,520. The k=2 scalar111 count is 3,036,140,820, but k=2 needs no
promotion, so this is not an assertion that that list is evaluated there.
[Reproducible arithmetic](../results/issue67-native/enumeration-envelope.json).

This is a source cardinality, not a claim that the entire list was allocated
or measured by a capped run. It explains why increasing a small native time
limit is unlikely to supply the intended acceptance fixture. A genuinely
shape-aware/streaming native enumerator with a proved semantic equality or
coverage/reconstruction invariant is a separate coordinated implementation
task. The Python S-only union proof is not a proof for changing this native
runtime. No replacement or proof-interface weakening occurs here.

## Resource protocol and a preserved failed launch

Initial source 80dd090b18bb0ed67d235b0f03cf6080e6c90a68 triggered isolated
Actions run35521735640. The default build, explicit dependency build, driver
typecheck, both terminal kernel replays and seven harness selftests passed.
No native fixture ran: the checkout's default shallow history omitted the
pinned base object, so the ancestry guard failed. This is preserved in
[initial-attempt.json](../results/issue67-native/initial-attempt.json), not
called a solver failure. Revision1f631178 changes only the NEW workflow's
fetch-depth to 0, retaining the strict source check.

The second attempt at 1f63117844d9a664317db1af8c7e450952fec6ce also passed
source checks and selftests, but every child aborted before any probe event
with `failed to create thread` under the original 2048 MiB address-space cap.
All 14 strict and six stress records remained process failures, not answers.
[Original launch evidence](../results/issue67-native/launcher-attempt.json).
No post-hoc negative verdict or solver mismatch is inferred.

The corrected experiment removes RLIMIT_AS, adds an explicit `lean -j1` and
launcher preflight, and samples process-group resident memory on Linux every
50ms with a 2048 MiB threshold. This is a DIFFERENT memory protocol, not a
matched performance comparison or an isolated diagnosis of which launch
setting caused the earlier exception. The poll may overshoot between samples;
observed group RSS/virtual size and wait4 lifetime max RSS are distinguished.
A separate fake child allocating 128 MiB against a 64 MiB threshold is killed
and recorded UNKNOWN. This verifies the guard, not any Lean semantic claim.

## Commands and limits

The final harness resolves the actual Lean binary using `lake env lean -j1
--print-prefix` and captures only the Lean path variables from Lake. Native
case command: `<resolved Lean>/bin/lean -j1 --run <absolute driver path> ...`,
with `lean/` as the working directory and that exact environment. This is
Lean's source/runtime execution, NOT a separately compiled native C binary
compiled from the probe. The driver has no replacement solver and its setup
and elaboration are included in per-case process costs.

Run from a full checkout of the pushed source revision:

```sh
cd lean
lake build
lake build +Subtail.EntailmentPrepared +Subtail.TerminalDecisionLazy
lake env lean Issue67NativeProbe.lean
lake env leanchecker Subtail.RankQueryDecision
lake env leanchecker Subtail.TerminalDecisionLazy
cd ..
python3 experiments/issue67_native_probe.py --mode selftest --output /tmp/issue67-native/selftest.json
python3 experiments/issue67_native_probe.py --output /tmp/issue67-native/acceptance.json
python3 experiments/issue67_native_probe.py --mode stress --output /tmp/issue67-native/stress.json
```

Strict and stress defaults are 20 seconds wall, 18 CPU seconds per child and
2048 MiB sampled resident threshold; workflow outer cap is 15 minutes.
The Linux source/runtime and environment are pinned in receipts. The driver
uses `-j1`, LEAN_NUM_THREADS=1, LEAN_STACK_SIZE_KB=32768 and hash seed2026092067.
There is no random fixture search. The final direct Lean child is killed when
necessary and reaped; cleanup also signals any remaining process-group
members. wait4 records the actual Lean process CPU and lifetime max RSS even
after a limit; separate /proc sampling records a group peak with its sampling
limitation explicitly retained. A raw stress UNKNOWN is accepted as a
DIAGNOSTIC, never as solver success or NO. A strict UNKNOWN/FAIL fails the
acceptance command. Missing, duplicated or mismatching result fields fail,
as does a printed true marker from a nonzero-exit process.

Local Python selftests and an E061 supervision replay used a partial five-file
snapshot in `/mnt/data/issue67-native-source/snapshot`, separate worktree
`/mnt/data/issue67-native-work` and outputs `/mnt/data/issue67-native-runs`.
The synthetic local snapshot commit is NOT the GitHub base. Local native
Lean and full-repository tests were NOT RUN; the actual full-checkout native
runs are the named GitHub Actions executions. Unknown other workspaces and
stashes were not inspected or modified.

## First successful native run and CPU-accounting correction

At `05a30a1bcc873d7812b04c8c2e13c67c408fc477`, Actions run35522151478
(job106107964138) completed the native suites: 14/14 strict PASS and six
stress UNKNOWN at the 2048 MiB sampled RSS threshold. The native phase
probe reached `begin_preimage=1` but no `completed_promotion` marker.
The [retained receipt](../results/issue67-native/lake-parent-receipt.json)
records the exact interpretation and links the original raw artifact.

A resource-accounting limitation was then identified: when the entire
Lake/Lean group is killed, wait4 of the Lake parent need not include its
unreaped Lean child. The small wait4 CPU/RSS values in the six capped rows
are therefore launcher-only/incomplete, NOT solver CPU or peak memory.
The separately sampled group RSS and wall time remain valid observations.
This issue does not erase the semantic outputs of the completed cases.

Correction `63b6edc4ff58287b49dec25b24137e1c706513e2` resolves the real Lean
executable and its environment before testing, then launches Lean directly
under the same wall, CPU and sampled-RSS limits. Source elaboration and
runtime execution are measured, but Lake/environment setup is separately
recorded. The driver and every existing solver definition remain unchanged.
This correction is not a solver optimization or a matched resource benchmark.

## Final native execution: exact result and resources

Tested source: `63b6edc4ff58287b49dec25b24137e1c706513e2`.
GitHub Actions [run 35522442916](https://github.com/mhenglein/subtail/actions/runs/35522442916),
job106108739428, completed successfully on 20 September 2026 at 16:22 UTC.
The [compact native receipt](../results/issue67-native/native-receipt.json)
transcribes the completed job log, including every case input/hash, observed
fields, user/system CPU, wall time and both memory measurements. It is not
represented as a downloaded copy of the original artifact.

The original unmodified reports are [artifact10608662760](https://github.com/mhenglein/subtail/actions/runs/35522442916/artifacts/10608662760),
17706 bytes, SHA-256
`317ee6bab8239b9500e29dd2d022c0582925f39fe9e47280aa624987ef5c9e46`.
They contain the complete source-hash manifest, runtime binary/environment
resolution, preflight and per-case outputs. The artifact was uploaded by the
actual workflow; this worker read its log and metadata through the connector.

Executed on Ubuntu 24.04.5 x86_64, Python 3.11.16, Lean 4.33.1 commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Lake 5.0.0-src+819816b.
Default build (53 jobs), explicit dependencies (49 jobs), driver typecheck,
and the two explicit kernel replays PASS. Tools/library caches were reused.
The full legacy regression matrix, fresh all-declaration axiom audit and
cache-free release reproduction were NOT RUN by this diagnostic workflow.
No new theorem or imported-runtime replacement is introduced.

Nine resource/result guards PASS. The strict native suite is **14/14 PASS**:
six supplied-reference inspections, five direct one/two-state boundary calls,
one no-final lazy gate, and two actual original-expression API calls. Every
inspection field matches the independent literal/DAG expectation. For the
positive and reversed-flag chains, native finishing is false at `0`, false at
`00` and true at `000`. The ordered, diagonal, empty-suffix and Bad variants
reject exactly as expected. This is native semantic-interface coverage, not
automatic compiler selection of those references.

The negative expression input is rejected through the candidate-address
guard; the positive one is accepted through the positive guard. Guard readback
is a separate diagnostic preceding the actual unchanged endpoint call, not
instrumentation inside that endpoint. Neither earns terminal-promotion
coverage. All 20 final native processes emitted entry events; no startup
failure or missing semantic observation is hidden behind these counts.

All six stress cases remain **UNKNOWN**, triggered by the sampled resident
threshold rather than the wall/CPU caps:

| Probe | Wall seconds | CPU seconds (user+system) | Lean lifetime max RSS MiB | Result |
|---|---:|---:|---:|---|
| Direct, 3 states, positive `00` | 5.273 | 5.265 | 2102.4 | UNKNOWN |
| Direct, 4 states, positive `000` | 4.005 | 3.997 | 2102.4 | UNKNOWN |
| Direct, 4 states, ordered-flag negative | 4.016 | 4.002 | 2086.5 | UNKNOWN |
| Lazy, 4 states, positive | 3.948 | 3.939 | 2082.4 | UNKNOWN |
| Lazy, 4 states, ordered-flag negative | 4.003 | 3.996 | 2104.4 | UNKNOWN |
| Explicit phase probe, 4-state positive | 3.999 | 3.991 | 2100.4 | UNKNOWN |

These CPU figures now measure the actual Lean process, unlike the retained
Lake-parent attempt. Overshoot beyond 2048 MiB is expected under 50ms polling;
the table is the observed lifetime maximum, not an enforced hard RSS ceiling.
Native strict calls total 8.1723 seconds wall and 7.7708 seconds user+system
CPU, excluding separately recorded environment setup. Individual strict calls
took 0.546-0.660 seconds and peaked at 817420-817600 KiB. The six stress calls
total 25.2422 seconds wall and 25.1896 seconds CPU. These are diagnostic process
costs including source elaboration/startup; no optimization comparison is made.

The phase trace is decisive about the observed boundary:

    safe_one_letter=true
    finish_clauses=4
    begin_preimage=1
    [resident-memory cap; no preimage_clauses or completed_promotion event]

Thus the first preimage was entered but no completed promotion was observed.
The direct/lazy endpoint probes returned no Boolean at their caps. Neither
the selected two-step witness chain nor k-2=2 is counted as successful native
promotion. The source cardinality above helps identify a candidate cause, but
no per-allocation profiler established that all resident memory came from the
raw piece list. The correct status is a measured obstruction, not a native
counterexample, a global memory lower bound or completion of #67.

Final tested new source SHA-256 values:

- Driver: `2a308e17873a82563d0357c3efea82ee1219613fa9631549af1956365e021ec0`.
- Runner: `ce2074ae804bd3265f7b480e6006dc4b1cb6ef3f1f7b1ed87b9187d3b924342b`.
- Workflow: `f2e7bb8b7f956a01e3dfaa948b5714e48952973f98704eb59f0a59001e6c460e`.

The final evidence-only commit adds this note and receipts without changing
those tested sources. Final source/record SHA and released paths are in the
#67/#37 handoff. No subsequent run is claimed for a records-only commit.

## Integration boundary

The new workflow is deliberately branch-specific and does not change the
shared Lean workflow, default import graph or production interfaces. A future
integrator may adopt the small strict subset after review; the six resource
probes must remain diagnostics and not be converted into negative answers.

The prior independent S-only proof review and full-checkout E061 replay are
complete, but this new diagnostic harness has not received a separate
agent/human review. Typechecking, kernel replay of imported modules and test
agreement do not establish an all-input theorem for the harness. No new
closure, complexity, witness-bound or entailment theorem is claimed.

Required future work remains a genuinely successful automatic two-promotion
native terminal call and, separately, a full-expression frontend case that
reaches that terminal path without the positive/candidate/UNSAT shortcuts.
The S-only restricted union regression already integrated as E061 is not a
replacement for either. The native enumeration count motivates an exactly
specified shape-aware or streaming refinement with independent coverage and
reconstruction proofs; such a refinement needs its own coordinated scope.

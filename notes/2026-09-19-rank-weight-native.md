# Native quantitative follow-up: route and evidence

Date: 2026-09-19. A017/A018, C080; #30, #34, #37.
Actor: ChatGPT `rank-weight-native-20260919`, continuing its own advisory report,
not an independent review of that report.
Base: `3ce7cf18899ad24a5562d4b614f738bec8bc8427`.
Prior ordinary proof/counterexample: [PR #47](https://github.com/mhenglein/subtail/pull/47),
report at `42be43f35a98d4d23a4ba26439833730bbcd6510`.

## Ordered route

1. Prove a native counterexample against the unchanged enumerator and compiler:
   terminal five-state instance; input weight 17; the 35 forward/wrap repetitions
   per each of five atom occurrences; original Bounded and validity; emitted
   clause membership via mem_preimageClause; output weight 12+30*2^175 and strict
   violation of the old U. Do not evaluate the full enumerator or materialize
   observer controls. Kernel-reduce only structural size projections.
2. Separately prove a sufficient weight theorem for the unchanged construction.
   The advisory proof uses total piece occurrences M <= 6*T^2, at most 2*T mark
   groups, and interval observer size 6*k*product(active sizes). One physical
   interval still has ONE generator, even with repeated observation coordinates.
   The target is 64*k*T^(6*T^2+2), not a redefinition of closureBound/ClosureFor.
3. Only after the single-step theorem: shortest accepted shared-interval product
   paths after all marks and boundary controls have been fixed; length at most
   N*W over all intervals on an N-vertex base; reconstruct an extension with at
   most N*(W+2) vertices; unwind the larger T/F recurrence. State k separately
   from original subtype-input size and do not assume the remaining reduction.

Each stage has its own completion/evidence status. The qualitative terminal
Boolean theorem uses none of these new quantitative results and is untouched.
No shared definitions, interfaces, import aggregator, toolchain or existing
workflow is changed. PR #47 and other workers' contributions remain preserved.

## Initial validation status

The native regression and isolated check workflow are submitted for compilation;
no new native success is claimed until the exact-head logs and kernel replay are
read back. The current container has Python 3.13.5 but no installed Lean and DNS
lookup for github.com failed. GitHub Actions supplies an isolated pinned Lean
4.33.1 runtime. Per job: 25-minute wall timeout, 6 GiB virtual-memory limit,
1200-second CPU limit per process; subprocess build/replay/audit timeouts are
900/600/300 seconds. No random seed is involved.

Run on a prepared checkout:

```sh
python3 scripts/check_rank_weight_native.py
```

The script compiles each listed additive target explicitly, runs leanchecker,
checks transitive #print axioms closures against propext/Quot.sound/Classical.choice,
and records exact source hashes and checkout/source revisions in a scratch JSON.
The source gate rejects unfinished placeholders, unsafe code and compiled proof
oracles. Compilation alone is not the final acceptance gate.

Satisfiability of the particular oversized clause remains the separate ordinary
model in PR #47 unless explicitly strengthened below. The universal original
weight conjunct has no satisfaction premise, so emitted membership and the exact
size violation suffice to refute that concrete contract.

## Handoff

Update this section with exact completed statements, source hashes, native
outcomes and any failures or uncompleted stages before releasing the scope.
Shared STATE/C080/A017/A018 updates remain integrator-owned. This report does not
promote Problem 1.7 or an explicit witness bound by merely passing a fixture.

# Primitive-table solver: proof and measurement readback

Date/session: 2026-09-20, solver-profile-20260920. A010/A018, C081,
E058; #60 under #37. Base `3ce866e`. This is an implementation refinement
for the existing arbitrary-tree theorem, not a new decidability or complexity
claim. The ordinary proof route is in [the construction note](2026-09-20-solver-profile.md).

## Exact proof boundary

`EntailmentPrepared.materialize_eq` quantifies over every natural number of
controls and every Boolean epsilon/push/pop system. It proves equality of all
five transition functions, including the zero-control case. `prepare_eq`
then proves equality of the complete dependent machine/cache record.

The prepared `safeCheck` and `derivedCheck` run the existing generic path tests.
`separationCheck_eq` preserves the exact `pathList`, forced seeds, denials and
target address; `satCheck_eq` preserves satisfiability. `afterPositive_eq`
preserves the ordered candidate scan and the same complete terminal fallback.
`normalizedWithPaths_eq` works for every list, including an empty one.
`entailsCheck_eq_fast`, `entailsCheck_correct` and `entailsCheck_eq` connect the
original finite syntax to the existing fast and reference algorithms and to
arbitrary-tree entailment. These theorems have no supplied bound or promise.

The `Prepared` structure itself stores only runtime data. Its public fields do
not certify arbitrary hand-built records; the equality theorems concern the
record returned by `prepare`. All runtime definitions are audited independently
of the proof declarations. No source file in the original proof, finite-tree
endpoint or default import graph was modified. The paper's pinned source
blobs and old benchmark receipts are retained unchanged.

## Independent source review

A separate read-only reviewer inspected the exact module and ordinary argument
at `e3d581d`, including the dependent record equality, all branch conditions,
seeds, candidate order, complete fallback and runtime sharing intent. The
[readback in #60](https://github.com/mhenglein/subtail/issues/60#issuecomment-5748135912)
found no semantic blocker. It is a review of the supplied implementation, not
blind rediscovery of C081. The reviewer ran no native build or benchmark.

A second reviewer audited the diagnostic protocol, then separately implemented
the matched benchmark harness. Review findings included missing completion
markers, result ordering, family/result semantics, platform-specific caps and
bounded output handling. The profiler now rejects malformed completed traces
and never accepts a Boolean from an interrupted process.

## Measurement boundaries and retained failures

Initial `#eval` instrumentation at `7e03916` lost partial trace output when
Lean was killed. `--run` fixes this diagnostic issue; matched benchmarks keep
the original `#eval` invocation. The initial receipt remains provenance.
A preparation-only ablation at `d712a40` solved supplied depth twelve but moved
expression depths six and eight into a slower candidate-separation phase.
The accepted implementation reuses the same primitive tables in both stages.

Each phase timer forces a summary and includes trace overhead. Supplied-address
rows test a component and use true for separation; expression rows call the
full decision and use false for non-entailment. Neither is evidence that the
finite candidate list is complete. No peak-RSS value was available on this
host, so no memory improvement is claimed.

The first draft needed ordinary elaboration fixes for let reduction and the
`Config` namespace; no theorem statement changed. The first CLI smoke checker
incorrectly expected exit zero for `UNKNOWN`; the CLI correctly returned its
documented exit two. The checker was repaired at `bdd3fee` and rerun. Neither
failure was a solver disagreement.

## Reproduction and final evidence

Run in an isolated checkout using Lean 4.33.1, one Lean thread and the existing
wb-marcus environment. The full measurement and review status will be pinned
here after the combined-tree checks finish. No uncompleted gate is a PASS.

```sh
python3 scripts/check_prepared_summary.py --cli --output tmp/prepared-audit-cli.json
python3 experiments/profile_entailment.py --output tmp/profile-baseline.json --scratch tmp/profile-baseline
python3 experiments/profile_entailment.py --primitive-tables --output tmp/profile-tables.json --scratch tmp/profile-tables
python3 experiments/profile_entailment.py --prepared --output tmp/profile-prepared.json --scratch tmp/profile-prepared
PYTHONPATH=scripts python3 -m unittest scripts/test_subtail.py scripts/test_finite_trees.py scripts/test_profile_entailment.py
python3 scripts/check_lean.py
```

The production CLI's timeout includes build and explanation work. Matched
benchmarks build first, then cap each fresh Lean query at 20 seconds wall and
CPU, 16 GiB Linux address space, one thread and a 32768 KiB Lean stack.
Python parsing, process control and countermodel extraction remain outside the
Lean proof. The finite-tree endpoint and raw terminal backend remain unchanged.

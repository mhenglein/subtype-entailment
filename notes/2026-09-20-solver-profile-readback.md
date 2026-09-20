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

The final proof/CLI audit and matched benchmark ran at
`20e31a8829a77975e2fc10ba2aa494451b9586af` in an isolated wb-marcus checkout,
using Lean 4.33.1 and Python 3.13.14. All executed source hashes match the
integration candidate. [Combined source-pinned receipt](../results/solver-profile.json).

| Exact generated input | Prior fast endpoint | Prepared endpoint |
| --- | ---: | ---: |
| Supplied separation, depth 12 (component) | UNKNOWN at 20 s | 1.220 s |
| Nested original expressions, depth 4 | 12.550 s | 1.019 s |
| Nested original expressions, depth 6 | UNKNOWN at 20 s | 1.721 s |
| Nested original expressions, depth 8 | UNKNOWN at 20 s | 3.827 s |

These are single-run, same-host uninstrumented wall times including Lean
startup, after module builds. They are workload-specific measurements, not
an asymptotic bound or an estimate of the interrupted baseline's finish time.
The generated suite improves from 16/19 to 19/19. The original 38 fixtures
remain 33 completed and five UNKNOWN for both variants: 26 frontend, five
normalized and two raw cases complete. All five raw limits use the unchanged
terminal function. There are no completed Boolean disagreements or oracle
failures.

The prepared component check passes for 62 systems. Six vector-length/two-
checksum comparisons cover 740 primitive bits, 148 forward and 148 reverse
balanced bits, 148 control-path bits, 12,884 arbitrary reachability bits and
1,292 control-reachability bits. This compact differential has a checksum
collision boundary and does not replace the all-input theorem.

The fresh build, bundled `leanchecker` replay and all 24 declaration closures
pass; none of the 13 runtime declarations uses classical choice. Five actual
CLI checks pass, including depth-six/eight negative decisions with valid graph
countermodels and separating paths `0^6`/`0^8`, and a cap returning UNKNOWN
with exit two and reason `time_limit`. Graph checking and extraction remain
Python. The default core was freshly built, kernel-replayed and differentially
checked at `bdd3fee`; its executed source bytes are identical in the candidate.
It reports 80 instances, 10,160 word comparisons and zero failures, plus the
existing budget, suffix and two-state checks. Old receipts were restored
unchanged after copying the fresh result into this experiment.

```sh
python3 scripts/check_prepared_summary.py --cli --output tmp/prepared-audit-cli.json
python3 experiments/check_prepared_summary.py --components --benchmark --generated --compare-baseline --output tmp/entailment-prepared.json
python3 experiments/profile_entailment.py --output tmp/profile-baseline.json --scratch tmp/profile-baseline
python3 experiments/profile_entailment.py --primitive-tables --output tmp/profile-tables.json --scratch tmp/profile-tables
python3 experiments/profile_entailment.py --prepared --output tmp/profile-prepared.json --scratch tmp/profile-prepared
PYTHONPATH=scripts python3 -m unittest scripts/test_subtail.py scripts/test_finite_trees.py scripts/test_profile_entailment.py
python3 scripts/check_lean.py
```

Final local checks pass: 68 focused Python tests, the 18-approach/164-record
research index, paper source/map checks and the diff guard. The final
[harness/CI review](https://github.com/mhenglein/subtail/issues/60#issuecomment-5748223410)
confirmed exact fixture identity and routing, and identified missing explicit
CI acceptance gates. The workflow now pins the fixture manifest, requires 38
original rows and seven valid raw outcomes, and checks all completed answers
against the existing E055 baseline step. It does not run a redundant third
baseline. A [final read-only check](https://github.com/mhenglein/subtail/issues/60#issuecomment-5748245108) confirmed these gates and released the review scope.
The exact workflow assertions were executed locally on the actual
paired results represented in that prior receipt schema. This is an assertion
check; GitHub CI status is recorded separately at publication in #60/#37.

The production CLI's timeout includes build and explanation work. Matched
benchmarks build first, then cap each fresh Lean query at 20 seconds wall and
CPU, 16 GiB Linux address space, one thread and a 32768 KiB Lean stack.
Python parsing, process control and countermodel extraction remain outside the
Lean proof. The finite-tree endpoint and raw terminal backend remain unchanged.

# Source-walk scheme cost and terminal-suffix switching

Date: 2026-09-13. Base `4ce1d6b5d20d3fa39a5c4f72d9c96da24e56356a`.
A009 records the dated attempt; A008/A017 and Q004 are affected.

**Written proof and reproducible finite checks. Independent mathematical review
pending; no Lean verification. Unrestricted Problem 1.7 remains unresolved.**

[Full proof, constructions, attempted closing route and limits](../notes/2026-09-13-scheme-cost-and-switching-audit.md).
C048/C050 supply the earlier synchronization/counter construction. The new
lower bound concerns the variable-base C075 scheme cost, not construction
priority, a runtime lower bound, or general undecidability. The auxiliary
switching solver overlaps the earlier target-frontier class; it is not claimed
as a new cover for recurrent targets.

## Claims

<a id="c076"></a>

### C076 — Exact exponential minimum source-walk scheme cost

**Statement.** For every d>=1 the stated binary terminal instance I_d has at
most 18d^2+11d+8 states and exactly one witness Wd=(E(Cd)00)^(d+2), where Cd
lists all d-bit counters least-significant bit first and E(0)=10,E(1)=11.
For the precise C075 syntax, charging one per phase plus every explicitly
listed base-source arrival, its minimum scheme cost is exactly
`(d+1)*(d*2^d+1)`. The same minimum holds after every semantically dead flag
has been removed. Hence no polynomial-cost cover in this syntax exists.

**Proof.** Append a universal last component to the prior counter/synchronization
family. Every visited source has an explicit live comparison into that component.
Length-d counter windows at the same phase uniquely reconstruct their counters.
Every source-pivot loop consumes a positive multiple of d data bits within one
stage, so two consecutive copies would contradict that injectivity. No phase
can use exponent greater than one; its cost equals its covered source visits.
Plain phases attain the resulting exact minimum.

**Status and limits.** WRITTEN PROOF + REPRO, independent review pending, not
Lean. This is a description-size obstruction, not a refutation of a larger
computable bound, Q004, C075's supplied-scheme theorem, or a different shared-word
representation. These inputs remain decided by the existing DFA-intersection
method. No independent re-certification of the full subtype bridge is claimed.
[Detailed proof](../notes/2026-09-13-scheme-cost-and-switching-audit.md), E048.

## Experiments

<a id="e048"></a>

### E048 — Exact scheme-cost, phase-window and live-source checks

**Command.**

```sh
python3 experiments/scheme_cost_barrier.py --self-test --output /tmp/scheme-cost.json --full-output /tmp/scheme-cost-full.json
cmp results/scheme-cost.json /tmp/scheme-cost.json
```

[Implementation](../experiments/scheme_cost_barrier.py),
[compact evidence](../results/scheme-cost.json).
The full output regenerates all 565 liveness certificates and concrete optimal
phase partitions. Six family widths d=1..6 have exact costs 6,27,100,325,966,2695.
Additional checks cover 518 common words, 642 bit corruptions, 20,320 four-oracle
word comparisons, 8,158 phase-window reconstructions and 54 phase-aware automata.
E049 separately compares the fixed-word optimizer with an exhaustive literal
partition oracle. Counts are finite evidence; the all-d theorem is the written
proof, not a conjecture inferred from the six rows. Seed 2026091361.

<a id="e049"></a>

### E049 — Supplied suffix-switch solver and independent cost partitions

**Command.**

```sh
python3 experiments/check_suffix_switch.py --output /tmp/suffix-switch.json
cmp results/suffix-switch.json /tmp/suffix-switch.json
python3 experiments/suffix_switch.py --demo
```

[Solver and compiler](../experiments/suffix_switch.py),
[checks](../experiments/check_suffix_switch.py),
[compact evidence](../results/suffix-switch.json).
Sixteen acyclic compiled-instance oracles plus sixty fixed-master graph oracles
are exhausted: 15 YES,61 NO. There are 2,426 finite candidate words, 1,452 five-way
structured comparisons, 8,191 raw binary words, 244 exact fixed-word partition
oracles, and explicit shared-assignment/cap cases. Seed 2026091362.

**Exact scope.** Finite-control switching among marked suffixes of one shared
terminal master with arbitrary regular edge/master/output guards. The algorithm
exhausts finite joint actions and finite control/output graphs, without SMT;
caps return UNKNOWN. Its targets remain confined to the final master. This
supplied class overlaps C054-C056 and does not establish new general coverage.
Its all-length correctness argument is Section 6 of the proof note. The auxiliary
class is recorded as a scoped implementation, not a new global breakthrough.

## Integration and handoff

Both deterministic commands were run and replayed with byte-identical compact
outputs in the integration session. Four separately implemented word predicates
are not an independent mathematical referee. No Lean build or full local
repository test suite was run. The dedicated read-only CI job validates the
canonical index/links and replays both outputs on the integrated checkout.
Consult the workflow result before treating that remote check as passed.

The next unrestricted obligation is still a total computable existence-preserving
cover or another exact treatment of interacting recurrent targets and changing
shared words. Polynomial C075 cost is no longer a viable strengthening. The
existing C075 theorem and Q004 remain intact at their stated evidence levels.

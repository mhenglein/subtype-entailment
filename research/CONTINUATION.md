# September 4 continuation: claims, evidence, and next target

This extends [C001-C020](claims.md), preserving the original claim history.
The first checkpoint is commit `e93f035`; the later denial-aware continuation
is described below. **Unrestricted Problem 1.7 is not settled.** All new proofs
are written mathematical arguments, not Lean-checked statements. None carries
a literature-priority claim.

## Claim extension

| ID | Established statement | Scope and evidence |
|---|---|---|
| C021 | A k-state one-flag family has exact budget 2k-4 and shortest length 3k-3. | Abstract instances; [proof](../notes/2026-09-04-budget-growth-family.md), E016. No subtype realization claimed. |
| C022 | At most three states: witness length at most six and budget at most two, both sharp; equivalent to nonempty Necessary(1,1). | [Written proof](../notes/2026-09-04-three-state.md), E017. Binary census, finite-alphabet proof. |
| C023 | Every positive successor of an actual accepting summary class has empty A subset and empty incoming flag column. | Joint W/F/G invariant; [proof](../notes/2026-09-04-summary-absorption.md), E018. Also holds with denials. |
| C024 | Total, Bad-free absorbing instances admit an exact graph decision with a padding witness. | Includes denial-free normalized subtype outputs through the audited bridge; same proof and E018. |
| C025 | On satisfiable normalized inputs, safety is exactly avoidance of B(u) intersect D on every prefix. The separate S subset component is redundant. | [Denial-aware proof, Section 1](../notes/2026-09-04-denials-and-continuations.md), E019. The SAT guard is essential. |
| C026 | After a supplied safe prefix enters the zero-column final region, existence of any safe witnessing extension is decidable by a finite periodic-ray product. | Same proof, Section 2; E019. NO_EXTENSION is local, not unrestricted NO. Complete entry-frontier decision when the safe pre-zero region is acyclic. |
| C027 | A reachable safe cyclic zero-region vertex with two safe outgoing letters supplies a cubic-length witness certificate. | Same proof, Section 3; E019. The alternate edge may exit the cycle. Absence of the certificate is not NO. |
| C028 | An actual eight-variable subtype system has exactly the separating paths 11 0^n 1, n>=1. Its shortest witness needs a pre-final loop, and every separating path is terminal. | Same proof, Section 5; E019. Refutes repeated-state deletion and completeness of an infinite-extension-only decision. |
| C029 | Existence of a witness admitting an infinite safe continuation is decidable for absorbing instances, including arbitrary pre-final loops. | Same proof, Section 4; E020. A finite periodic-suffix monitor handles pure tails. NO_INFINITE_EXTENSION does not rule out terminal witnesses. |

The C029 bound H_infinity(k)=2 k^2 (k+1) 2^(k^2) is a generous witness-length
bound for that category only. It must not be advertised as the missing global
budget bound. Infinite continuation of a path is not infinite-tree semantics.

## Experiment extension

| ID | Command | Saved evidence and coverage |
|---|---|---|
| E016 | `python3 experiments/check_budget_growth_family.py` | 28 parameter pairs; every lower budget split exhausted; 70,680 direct shortest-word comparisons. Checkpoint digest: [import record](../results/continuation-import.json). |
| E017 | `python3 experiments/three_state_decision.py` | All 65,536 normalized three-state binary instances; all negative Necessary(1,1) graphs exhausted. Same import record. |
| E018 | `python3 experiments/check_summary_absorption.py` | 400 independent denial-free normalized systems; 281 YES and 119 NO. Same import record. |
| E019 | `python3 experiments/check_unrestricted_continuation.py` | [Result](../results/unrestricted-continuation.json): 500 systems; 24,129 full/reduced/canonical comparisons; 45,615 periodic predictions; actual terminal obstruction. |
| E020 | `python3 experiments/check_infinite_extensions.py` | [Result](../results/infinite-extensions.json): 1,500 abstract instances and 400 additional subtype systems; 305,010 monitor comparisons; 502 exact small-state checks. |

The new independent bridge validates positive countermodels using exact regular-
language operations, without a stack-depth cutoff. It does not replace a formal
all-input verification of the existing bridge. The full original repository
suite and Lean build were not rerun in this continuation. The new E019/E020 checks are separate commands; they are not yet wired into
the original repository workflow.

## Next research target

The exact remaining alternative is **terminal safe witnesses with unbounded
pre-final histories**. A witness with no infinite safe continuation can be
extended to a terminal safe witness in at most k-1 additional letters. C029
settles the other alternative. C028 proves that the terminal alternative is
nonempty and that shortening by repeated states is unsound on actual outputs.

For A013, work on a complete finite abstraction or a computable bound for that
terminal branch. Preserve the shared B/A/D structure; abstract flags alone lose
it. For A008/A018, the three-state classification and periodic-suffix monitor
provide precise formalization targets. For A009, B>|K| is already achieved;
future universal abstract bounds must accommodate at least 2k-4.

# Subtype summary bridge: route outline

Date: 2026-09-19. A010/A018/C080, #31/#37.
Actor: bridge-continuation-20260919. Base 9508e8c6455140012d21e0919985ec3c17144a64.
Initial status: proof attempt; no full subtype decision yet.

## Finish line and unresolved implications

The final goal remains an executable Boolean equivalent to subtype entailment
over arbitrary prefix-closed product-node sets, with finite bottom/product
syntax and no top constructor. Existing normalized satisfiability and
canonical separating-address theorems are exact inputs.

This contribution works forwards from those reachability theorems and backwards
from the terminal decision backend. Its precise targets are:
1. Prove forced-root plus ordered-cut characterization of membership at the
   separating address. Include all prefix seeds, diagonal flags and empty suffix.
2. Construct a finite executable summary Instance and prove original Witness
   equivalent to separationCheck, including UNSAT via a global Bad bit.
3. Derive empty-incoming-column absorption from the actual reverse-pop alphabet.
4. Independently prove absorbing safe extension and the C031 same-state
   terminal restriction, with the infinite branch defined by a safe cycle.

Still unresolved after those implications: the exact finite C029 periodic
monitor/existence decision, normalization of arbitrary finite compound syntax,
and their final total executable composition. No missing reduction or numerical
witness bound may appear as an implicit hypothesis of a claimed full result.

## Proposed two-summary construction

States are pairs of finite subsets B,A of the normalized controls, represented
by explicit subset enumeration. Initially B and A are balanced closures of
alpha and beta in W and reverse W. Reading a letter advances each subset by a direct pop followed by a balanced
path. Reachable subsets are already balanced-closed; last-letter decomposition
of Pop proves this transition exact for those subsets. No such exactness is
claimed for arbitrary non-closed subsets. Flags on ordered state pairs mean B_left intersects
A_right. Finals mean A avoids Forced.

Let Danger(m) mean some denied control has an arbitrary-word Pop path to m in
reverse W; existing finite controlEdge/pathCheck decides it. Mark a summary Bad
if C is unsatisfiable or B intersects Danger. The Witness predicate already
checks every prefix, so all earlier-prefix denial checks should collapse to
this one local test at every cut. This removes the third denial subset used by
the original implementation; the equivalence must be proved and independently
reviewed, not inherited by analogy.

A final A contains no forward push target. Reverse-pop letter edges therefore
have no source in A; one letter produces empty A, hence another final with an
empty incoming flag column. The proof must preserve epsilon closures.

## Validation

Ordinary proof and adversarial readback; exact independent literal predicates
and existing supplied-address checks; pinned Lean builds, kernel replay and all
new-declaration dependency audits with no Classical.choice in runtime code.
Keep distinct the all-word theorems, finite regressions, remaining assumptions
and practical runtime limits. Use separate worktrees and a single integrator.
If a simplification fails, preserve its minimal counterexample and retain the
three-summary route as a repair; do not weaken arbitrary-tree semantics.

## Compiled bridge checkpoint

`SummaryBridge` proves the exact ordered-cut, forced-root and prefix-denial
characterizations. `SummaryAutomaton` explicitly enumerates every pair of
control subsets, defines all annotations and transitions, and proves
`witness_iff_separation`, `not_entails_iff_witness`, and `summary_absorbs`.
The latter quantifies over every enumerated state, including unreachable ones.
All-word Lean compilation passed on the pinned toolchain; kernel replay,
complete dependency audit and executable regressions are still pending.

The independent read-only reviewer checked the construction against base
9508e8c and the ordered-cut proof source. The reviewer identified the needed
reachable-closure boundary and confirmed arbitrary-state absorption. Final
source readback is pending.

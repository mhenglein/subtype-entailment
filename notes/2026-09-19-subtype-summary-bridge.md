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

## Ordinary mathematical readback

Fix a finite normalized constraint list C and queried variables alpha,beta.
Let W be its concrete push/pop system. A tree is an arbitrary prefix-closed
set of binary addresses, so this step places no finiteness, regularity or
computability requirement on a model.

For a candidate address w, put B(u)={m: Pop_W(alpha,u,m)} and
A(u)={m: Pop_reverse(W)(beta,u,m)} at every prefix u of w. The explicit
physical state set lists every pair of subsets of the finite controls.
A transition takes a direct pop from a member and a balanced suffix. The
last-letter Pop decomposition proves that every reached state is exactly
(B(u),A(u)). Arbitrary non-closed subsets are permitted as unreachable states;
no Pop interpretation is claimed for their transitions.

Minimum-stack factorization says a prefix seed (alpha,u) reaches (beta,w)
exactly when some ordered cuts i<=j have a common Pop control and
w.drop(j) is a prefix of w.drop(i). The i=j and j=length(w) cases are included.
Forced-root seeds reach beta at w exactly when A(w) meets Forced.
A prefix seed reaches a denial at any stack exactly when some B(u) meets
Danger, where Danger is decided by finite reverse control reachability.
The separate satisfiability bit checks all forced-root denial consequences.
These are precisely the original Witness checks of the constructed instance.

Therefore not_entails_iff_witness is an exact existence equivalence, not an
executable search over all words. If a physical state is final, its A subset
contains no Forced variable. Every reverse-pop source is a forward push target,
which is Forced. Its next A subset is consequently empty; the successor is
final and has an empty incoming flag column. This proves strong absorption on
all physical states, with no reachability premise.

Independent source review at acf9e5bcd2465931a8a4bce485f70300e45172c9 found no
semantic defect in both modules and the inherited semantic interfaces.
The review read proofs and definitions but did not execute Lean. The author
separately ran the pinned build, leanchecker Subtail.SummaryAutomaton, and
scripts/check_subtype_summary.py: all 47 new declaration dependency closures
passed; runtime definitions have no Classical.choice. These checks apply to
the source at acf9e5b, not to any later integration wrapper until it is rechecked.

## Adversarial boundaries and remaining work

The earlier false weakening of absorption is retained: final-state closure
alone does not protect extension. With finals 0,1, edge 0--0-->1, no other
edge, and flag (0,1), the empty word is an original witness but the only
terminal candidate is forbidden. The needed hypothesis is an empty incoming
flag column at EVERY defined successor of a final state.

Terminal pruning must first remove edges incident with Bad or diagonal-flagged
states, then accept only safe ORIGINAL final states with no remaining edge.
A new nonfinal sink must stay rejecting, and an unsafe initial state must not
produce an empty witness. The safe-cycle branch will have an explicit original
witness, a finite safe stem and a nonempty safe cycle; it must not be replaced
by an unproved bounded search or by a stronger profile-preservation claim.

The unproved C029 obligation is an executable check for existence of such a
witness with a safe cyclic continuation, uniformly over finite absorbing
instances. A graph cycle reachable from the initial state alone is insufficient:
the prefix must satisfy all original ordered word comparisons. Normalization
of arbitrary finite bottom/product syntax and the final executable entailment
composition also remain separate. No conditional wrapper will be reported as
discharging these obligations. An obstruction to C029 should be tested against
its exact periodic-obstruction argument and, on the opposing route, for whether
it provides a true undecidability encoding rather than a failed finite monitor.

## Executed bridge regression and tooling checks

At source acf9e5b, `experiments/check_subtype_summary.py` passed all 1803
query-word pairs across 42 finite normalized systems. It compares the native
summary Witness and supplied-address checker with an independent P-automaton
predecessor saturation and a literal original word predicate. It also checks
528 physical states, 10752 ordered flags and every transition, plus 680
final-successor absorption edges. Seed: 2026091931. The one-control constraint
sets are exhaustive; two-control systems comprise named and seeded cases;
the three-control case tests the essential proper-prefix seed. Word lengths
are at most three (two in the three-control case). This is finite regression
evidence; the all-word claims rest on the theorems. Larger native summary
constructions were not benchmarked and no practical complexity bound is claimed.

The real configured Lean MCP on wb-marcus returned zero diagnostics for
SummaryAutomaton in 1.51 seconds and the exact reverse_next_empty proof goal
in 0.02 seconds on the same warm server. Earlier goal-driven compilation used
last-letter Pop decomposition to avoid a false arbitrary-subset exactness claim.
The source builds and dependency audits ran in an isolated persistent worktree,
separate from the terminal-restriction worker's Lake cache. Main's prior four
GitHub checks at 9508e8c were also read back as PASS; these are baseline checks,
not evidence for the current unpublished integration tree.

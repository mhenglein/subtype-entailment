# Global border-rank attempt (no new stable IDs)

Date: 2026-09-15. Baseline: 47adf83c194aa941b525240f6470f3d77a69f81d.
Workstream A017. Written arguments plus executed tests; independent mathematical
review pending, not Lean. No unrestricted decision is claimed.

[Full proof and failed global algorithm](../notes/2026-09-15-unrestricted-rank-attempt.md)
[Route outline](../notes/2026-09-15-rank-route.md)
[Implementation](../experiments/prefix_rank_layers.py)
[Independent checker](../experiments/check_prefix_rank_layers.py)
[Deterministic result](../results/prefix-rank-layers.json)

Every reversed terminal word has at most k-1 first-depth milestones. Each new
milestone ends at the first return of the preceding reference. Between returns,
a concrete reference and its full run yield an exact finite KMP/reverse-state
layer with all flags, including empty and full borders. This is an ALL-INPUT
finite-depth representation, not a finite symbolic cover.

The attempted finite quotient is false. A four-state example defeats choosing
a shortest first return at each endpoint. A six-state example also defeats
endpoint plus full transition action, visited-state set and entire agreement
profile. Its exact witness language is

    {0^a 1 0^(2b) 1 : a positive even, a<2b}.

The safe first returns 1 0^(2b) 1 have identical proposed signatures, but b=1
has no legal completion and b=2 gives the shortest witness 00100001. A change
of flags makes the exact continuation sets the disjoint singletons {0^(2b)}.
The underlying examples are flat and already covered by earlier exact methods;
they refute this proposed GENERAL quotient, not the earlier solvers.

A four-state one-live-flag family additionally shows unbounded complete-bipartite
minors in the successor-plus-failure graph even at failure depth two. Therefore
bounded failure-tree depth alone is not a bounded-width graph argument. The
same fixed instance has a short witness, so this does not refute an existential
bounded-width normalization.

The new fixed-reference checker is tested by whole finite-language equivalence
against an independent literal-window monitor. The general search procedures
return FOUND_WITNESS, UNKNOWN, or EXHAUSTED_HEURISTIC. The last of these is
explicitly NOT a NO certificate. The counterexamples have separate all-length
language proofs and directly checked witnesses.

## Integration handoff

The next mathematical obligation is an effective symbolic elimination of the
unknown reference choices and their future shared-word dependence. A bounded
number of levels is not enough when each level has infinitely many word-valued
choices. Neither a generic word-equation theorem nor a named pushdown model is
used without an exact construction and acceptance proof.

This record is an additive proposed checkpoint, not an assertion that GitHub was
updated. Current execution ownership, C/Q status, older claims and shared
trackers are unchanged. After review, append a scoped A017 history entry and
link this record from STATE without promoting the failed quotient. No agents
or independent reviewers were launched in this attempt.

## Exact repair: one unknown reference can be eliminated

[Finite-interface proof](../notes/2026-09-15-one-promotion-elimination.md),
[implementation](../experiments/one_promotion.py),
[independent checker](../experiments/check_one_promotion.py),
[result](../results/one-promotion.json).

A first-return extension C of a fixed reference B has every internal failure
link into B. Its next matching graph is a spine with resets into a fixed core.
Streaming construction and exact reachability projection yield finitely many
interface relations. This decides existential completion through at most one
new milestone without supplying or bounding C. Hence existence with maximum
reversed border depth at most two is decided for arbitrary terminal inputs.
The native method solves both failed-quotient fixtures.

A final return still increases rank; a three-zero terminal path exposed an
initial prototype mistake, corrected before saved results. Seven unary-path
regressions retain that correction. Three C046 modular fixtures are genuinely
positive but rank-two negative, preventing an unrestricted interpretation.

The construction is not yet proved closed under repeated promotion: the entire
C becomes the next core and introduces new addressable positions absent from
the old summary. A higher-level preservation argument is still missing. This
is the next route obligation, not an assertion that finite depth is sufficient.

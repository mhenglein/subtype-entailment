# Rank milestones: targeted Lean route

Date: 2026-09-18. Base main: `9e9d3ecfe1277bd6e7ea6aeffdf035c12e477f89`.
Foundation branch: `2fe18864e39a26f6dd256bf05bea166c8c6b3d20`.
Workstreams A018/A017. Author: ChatGPT, continuing the user-requested formalization.

Target: connect the already checked terminal border-cardinality bound to the
candidate's recursive rank and first-return decomposition. Reuse the literal
`borderLengths` definition. No witness bound or compiler correctness is assumed.

Route: define a computable maximum proper border; prove exact nesting of border
sets and the rank recurrence; prove that first threshold milestones have exact
rank, that successive milestones have the preceding milestone as failure parent,
and that no intermediate/full final return is skipped. Prove reversal invariance
and transfer the existing accepted-suffix bound to every reversed prefix.

Acceptance: pinned Lean 4.33.1 build, kernel replay and axiom closures for the new
public declarations, plus direct finite binary-word regressions. A proof failure
is a failed proof attempt, not automatically a mathematical counterexample. Do
not replace a missing implication with an axiom or unfinished proof placeholder.

Remaining globally: finite coloured graph surgery; bounded-diagram compiler and
both uniform preimage directions; quantitative repeated closure and executable
witness bound; arbitrary-tree semantic transfer. This work does not establish
any of those later obligations or change the candidate's proposed status.

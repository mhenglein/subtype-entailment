# Lean route for the proposed rank-query decision proof

Date: 2026-09-18. Base: 9e9d3ecfe1277bd6e7ea6aeffdf035c12e477f89.
Workstream A018 supporting A017. No proposed theorem is promoted by this plan.

Target: an executable Boolean decision on finite normalized subtype inputs,
with correctness quantified over arbitrary possibly infinite type trees.

Critical chain: terminal accepting paths have bounded border chains;
first-rank milestones correspond to first returns; first-return prefix graphs
admit uniform finite query preimages preserving ONE generated word; finite
rank elimination gives a concrete computable witness bound; finite search and
the independently audited semantic bridge give the required decision.

Initial formal target: the first structural implication. Reuse Subtail.Basic
rather than restating run semantics. Prove accepting-prefix freeness, proper
agreement state inequality, injectivity of border cut-state labels, and the
k-state border-count bound at every suffix. Count includes the empty border;
the nonempty count is at most k-1. No bound on word length is asserted.

Outcome and check evidence will be recorded after compilation. The failure-link
recurrence, graph surgery, uniform compiler, completeness of its enumerator,
quantitative witness bound and full subtype bridge remain separate Lean tasks.
Do not insert any of them as an axiom or present a theorem assuming them as
an unconditional decision. Inspect theorem statements and dependency axioms,
not only successful compilation or examples. A compiler failure may be a
library/indexing issue rather than a mathematical counterexample.

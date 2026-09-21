# Review packet: graph-only first-return preimage

Date: 2026-09-20. Actor: standalone-first-return-20260920-astra.
Base: 19b06d4fed9da635d9b911f0e908d04e4fc4b099.
Target: notes/2026-09-20-standalone-first-return-astra.md, Theorem FR and
bounded-p corollary. Related issues #72 and #37.

**Independent-review status: PENDING.** This file is an author adversarial
readback and a concrete independent-review request, not an independent review
certificate. No second model, human or separate agent reviewed the new
relational theorem in this execution. A differently implemented finite checker
is useful evidence but is not a substitute for that missing review.

## 1. What was reviewed previously, and what was not

The repository's notes/2026-09-17-rank-query-independent-review.md records a
separate AI-assisted, author-informed review of the old graph surgery and
whole-conjunction preimage argument, particularly Sections 2-3. Its original
quantitative Section 4 is explicitly superseded by the September 20 correction.
Nothing here relies on its false universal U estimate. The current ledger
records RankQueryCoverage.closure_iff as checked. This session inspected the
statement, manuscript and relevant source interfaces, not a fresh Lean run.

That inherited review supports the lineage of the prefix-graph extraction.
It does not certify arbitrary relational bases, the local-table formulation,
infinite-base semantic extension, or the bounded-p attachment corollary.
Those are the independent review target now.

## 2. Author adversarial readback

**Quantifiers.** One existential decorated generator is chosen for the entire
clause. In relational bases, equal emitted words alone need not fix the origin
trace. The diamond fixture has one word with two incompatible intermediate
origin colours: each observer is separately satisfiable, their synchronous
product is not. Core-path witnesses are independent only AFTER fixing H.

**Origin aliasing.** Different physical groups can share one origin. The
positive interval observer, not origin disequality, keeps them physically
separate. Coincident first/last/variable roles merge into one physical group;
observer controls are still recorded per visit, not per observer name.

**Portals.** Every fresh mismatch exit copies ALL corresponding base edges.
This makes each selected portal witness an edge of one reconstructed graph.
A semantics with a hidden once-for-all choice of a single outgoing target is
not covered. Suppressing S at old End is intentional for arbitrary base
graphs; on the old prefix graph S at End was absent.

**Seams and invisible intervals.** Every traversal is split at every global
mark, including other atoms' marks. Adjacent generator intervals share origin,
control and next letter. A product coordinate is retained for each traversal,
including repeated traversals by the same atom. With no active coordinates,
the generator and positive-length condition are still present.

**Empty and singleton cases.** Zero paths require one common initial/final
allowed control. They are not automatically true at equal endpoints. A
one-emission extension has no interval between distinct groups but retains
a genuine wrap self-loop. Tests distinguish an allowed empty path, a rejected
empty path, a real loop, and unequal endpoints.

**Bound discipline.** Product simplicity is imposed on selected witnesses for
coverage, not on every syntactically enumerated diagram or reconstructed path.
Only finiteness and the explicit block/mark envelopes are claimed. There is
no small universal clause-weight or shortest-witness conclusion.

**Hypothesis discipline.** Terminality and subtype provenance are not used by
the local theorem. SafeReference is retained for the specialization whose
right-hand side says globally safe word extension: an unsafe old vertex
survives any extension. First return is retained for literal prefix surgery:
B=0,C=000 has a final failure parent 2, not the proposed old endpoint 1.

**Extra entrances/inverse edges.** Two entrances can exceed the original
s+1 block count but obey p*s+1. Unbounded entrance sets and a fixed four-state
two-way pattern provide explicit product-simple families with unbounded
numbers of fresh blocks. These refute the stated proof's envelope, not all
possible preimage theorems, two-way methods or decidability results.

**Further strengthening not asserted.** Arbitrary attachments without a fixed
base-query definition, negated reachability, common path-label registers,
globally chosen functional resolutions of relational exits, and an optimal
necessary-and-sufficient characterization of admissible transformations were
not proved. The bounded-p corollary counts the original v_1 among its total
portal targets.

## 3. Execution evidence and limits

The independent standard-library program imports no repository module.
Literal prefix/suffix graphs are compared with separately implemented surgery.
It also evaluates observers by product BFS and compares a restricted synchronous
interval primitive with separately enumerated physical strips. The result file
records all caps, the source hash and counts. Both deterministic replays,
including PYTHONHASHSEED=72, are byte-identical; py_compile passes.

Reported counts: 192 structural equalities, 71 safe-base equivalences,
4,572 relational endpoint tests (1,536 accepted runs, including 176 empty),
173 joint mark checks, and 720 interval comparisons. These are finite checks,
not full diagram enumeration, a proof of FR, or a re-execution of the checked
prefix compiler. The finite corpus includes zero active observer coordinates,
nonfunctional bases, origin aliases, repeated traversals and incompatible
observations of one generated word.

## 4. Independent reviewer request

Read the theorem note independently of the implementation first. Identify
any counterexample or missing condition in the following precise contract:

    For every finite schema T of Section 1 and every query phi of Section 2,
    effectively construct Pre_T(phi) of that same grammar, uniformly for H,
    such that H |= Pre_T(phi) iff some ONE legal decorated g gives H[g] |= phi.

Check graph-class closure and endpoint identification; whether every path has
the claimed decomposition; the finite enumeration envelope; all local portal
pullbacks on relational edges; one shared product coordinate per traversal;
first-step and interval boundary controls; positivity and hidden early End;
fresh/core equality and disequality; and reconstruction of all atoms on one
graph. Then check the bounded-p corollary's fixed definability condition and
that its p includes the original entrance.

Please separately state the inspected commit/file hashes, ordinary mathematical
findings, source-inspection versus executed checks, and which of the broader
claims were not reviewed. Do not edit paper/**, compiler interfaces or shared
ledgers. Reply in #72/#37 or a PR review; a new review note should use a disjoint
path agreed with the integrator rather than overwrite this author's packet.
A review request is not evidence that somebody has accepted or completed it.

## 5. Proposed integrator-only documentation action

After independent review, consider an additive standalone note/module entry
for the finite-table relational theorem. Keep Theorem 7.1's current safe-word
statement and existing Lean interfaces intact. Describe its prefix-graph
specialization as an extracted existing result; mark the relational/bounded-p
versions as ordinary proofs until separately formalized. Link the obstruction
families, and distinguish failure of a bounded-decomposition proof from failure
of preimage definability. The proposed prior-work comparison is bounded and
must not become a priority claim. No wording change to the active manuscript
or shared scientific ledger is performed by this branch.

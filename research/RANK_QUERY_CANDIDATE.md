# Candidate unrestricted decision: rank-query preimages

**September 20 correction.** The old universal weight estimate
`64*k*T^(2*T+2)` is false for the concrete enumerator: a checked terminal
five-state counterexample emits a larger clause. The semantic compiler and
qualitative C081 decision remain checked. C082 proves the separate replacement
`64*k*T^(6*T^2+2)` and the resulting Fhat witness bound. The original F by itself
and a smaller existential compiler are not refuted. Earlier unqualified size
arguments and reviews below are superseded at precisely that point; the text
is preserved as history. [Exact correction and dependency audit](../notes/2026-09-20-post-c081-quantitative-integration.md).

## September 17 follow-up: full compiler and proposed witness bound

The [compiler follow-up](RANK_QUERY_COMPILER.md) now supplies the complete finite
syntactic diagram enumerator, shared-interval compiler, nested query tests and
an explicit recursive witness bound. Its status is PROPOSED COMPLETE ORDINARY
PROOF, independent mathematical review pending, not Lean-checked. The generic
implementation is resource-limited in practice; timed UNKNOWN results are not
negative certificates.

The missing-compiler statements below describe the PRECEDING checkpoint and
its publication. They are preserved as history, not the current implementation
status. The original candidate proof is unchanged. The new proof, code, tests
and exact limits are linked from the follow-up; they do not constitute external
review or promotion into the project's established results.

Date: 2026-09-15. Base: `47adf83c194aa941b525240f6470f3d77a69f81d`.

**CANDIDATE PROOF; NOT ESTABLISHED.** No stable C/E identifier is reserved.
Independent mathematical review and the complete symbolic compiler remain
outstanding. The finite kernel checks are not an executed unrestricted decider.
Do not change the status of Problem 1.7 solely on this candidate's publication.

[Full candidate argument](../notes/2026-09-15-candidate-rank-query-decision.md),
[route](../notes/2026-09-15-rank-query-route.md).

## Proposed closing statement

For every finite binary terminal instance, existential witness existence is
reduced to evaluating a finite existential regular-path query on finitely many
two-vertex initial prefix graphs. Reverse border depth bounds promotions by
k-2 after the first letter. A promotion's new graph segment has one entrance
from the old graph; proper mismatch/failure edges go back to the old graph,
and the new endpoint may wrap to that entrance. Exact graph identities include
the full endpoint, overlapping occurrences, state colours and forbidden masks.

The central proposed preimage lemma transforms a WHOLE conjunction of directed
regular-path queries on an unknown promoted graph into such a query on its old
graph. A product-simple path enters the new segment at most its observer's
state count, so finitely many jointly ordered marks suffice. Core stretches
remain regular-path atoms. All observations of a shared forward interval are
combined with one common generating walk in a finite-state product. No inverse
edges, negative reachability, path-label equality or arbitrary MSO is introduced.

If the all-length construction is correct, the query class is closed under
all required promotions, and backward syntactic elimination terminates at the
finite initial graphs. The existing C030/C031 semantic transfer would then
apply at its own recorded evidence level. The new claim is a candidate proof,
not an independently audited theorem or a claim of implemented general solving.

## Exact review target

Lemma 4 and Sections 5-7 of the proof: diagram completeness, the finite mark
bound, regularity of joint generator/observer interval constraints, functional
attachment targets, end-colour rewriting and closure under repeated preimages.
In particular, preimages must be computed jointly for a conjunction: separately
choosing a new reference for each path atom is unsound.

## Executed checks

```sh
python3 experiments/check_rank_query_graphs.py
python3 experiments/check_query_grafting.py
python3 experiments/run_experiments.py
```

[Graph construction](../experiments/rank_query_graphs.py),
[graph/kernel checker](../experiments/check_rank_query_graphs.py),
[shared-diagram substitution checker](../experiments/check_query_grafting.py),
[graph results](../results/rank-query-graphs.json),
[grafting results](../results/query-grafting.json).

The first checker includes 4,094 direct/literal prefix graphs, 826 first-return
extensions, 10,080 regular-path queries with 6,419 accepting diagrams, 122,640
word-predicate checks and concrete hierarchies through rank seven. The second
checks 2,108 satisfying joint substitutions, including 1,484 length changes,
and independently rechecks 4,758 path atoms. No full preimage compiler was run.

A converse-edge family explicitly defeats the single-entry hypothesis if
inverse failure edges are added. A shared-strip regression rejects incompatible
observations that would pass when checked against independent reference words.
Seven one-vertex extension cases and 45 unary terminal cases protect endpoint
wrap and final-promotion conventions.

## Publication and integration

**Publication confirmed on 2026-09-17.** The candidate checkpoint's nine native
files were added to main in commit `7aed36227dbf67ec23f5aaaaf0da2d3d94f53eeb`.
The preceding rank-hierarchy investigation's eighteen native files were added
in `e0396ea023301704a7b273d2c68d77142641a7dd`, including its one-promotion
algorithm, failed-quotient counterexamples, discovery scripts and saved results.
See [the prerequisite record](RANK_ATTEMPT.md).

A fresh publication check compared all twenty-seven expected Git blob hashes
from the two supplied archives with main at `e0396ea`. Reconstructing its tree
with those hashes returned the identical tree
`f886167d2f964fa55309f8bcff30b4a5f9554a6b`. The archived native files therefore
matched the published files byte-for-byte before this publication-note update.
No mathematical source, implementation or saved result is changed here.

The publication commits record their September 17 deterministic test replays.
This status update independently checks publication integrity; it does not
claim a new test run, full repository CI, independent mathematical review,
Lean verification, or execution of the complete preimage compiler.

**Historical delivery limitation.** The original September 15 packages were
unpublished because their session lacked a working GitHub write path. Their
preserved notes and manifests describe that earlier delivery, not the current
repository status. The candidate remains CANDIDATE PROOF, NOT ESTABLISHED.
Review of Lemma 4 and Sections 5-7, and a complete symbolic implementation,
remain outstanding; publication does not settle Problem 1.7.

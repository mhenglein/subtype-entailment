# Candidate unrestricted decision: rank-query preimages

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

The active GitHub connector provides reads but no create/update action, and the
CLI could not resolve github.com. This checkpoint is delivered as a package and
an additive patch. No push or remote commit is claimed. Recheck current main,
review the proof, and preserve the other agents' records during integration.

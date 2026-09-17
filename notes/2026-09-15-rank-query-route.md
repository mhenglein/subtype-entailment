# Candidate query-elimination route

Research date: 2026-09-15. Repository base: 47adf83c194aa941b525240f6470f3d77a69f81d.

Target: an unrestricted terminal BorderAvoid decision, then the existing C030/C031 transfer at its recorded evidence level. Preserve arbitrary-tree subtype semantics. This is a research attempt, not an independently certified solution.

Proposed chain:

1. Reverse witnesses; terminality bounds their maximum nested-border depth by k-1 (previous rank checkpoint).
2. Use exact KMP prefix graphs, including failure, successor, both total prefix-transition edges, state labels and finite forbidden-source masks.
3. Growing a reference to its first return adds a forward strip. Edges from the old graph enter only its first vertex; all other strip exits go to the old graph, except the new endpoint's wrap to that first vertex.
4. Prove an effective preimage lemma for existential conjunctions of DIRECTED regular-path queries under one such walk-guided strip extension. Query product paths need only finitely many strip entries; finitely many marked positions partition one common generating walk into regularly constrained intervals.
5. Iterate the syntactic preimage operation a finite k-2 times, not a concrete reachability-summary substitution. Evaluate the resulting query on the finite one-letter graphs.

Critical obligations: exact graph-extension identities, every incoming fresh edge accounted for, synchronous observers over one common generated strip, closure of the query syntax, finite diagram bound independent of the unknown strip length, and endpoint/full-return handling. Arbitrary converse edges, negative path predicates and path-label equalities are outside the proposed closure lemma. The actual witness query must not need them.

Code tests will audit those obligations but will not alone prove the general preimage lemma. A full compiler and independent mathematical review are not yet supplied. Do not claim a native unrestricted decider from bounded reconstruction tests.

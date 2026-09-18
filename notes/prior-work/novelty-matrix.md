# Claim-by-claim novelty matrix

**Status vocabulary:** “promising” means no subsuming theorem was found in the inspected sources. It is not a priority claim.

| Subtail claim | Closest prior work | Material overlap | Candidate distinguishing content | Missing verification | Safe provisional wording |
|---|---|---|---|---|---|
| C067: all single-source binary terminal instances decidable; PSPACE upper bound | N&P 1999 decidable syntax; N&P 2003 cap equations; Breuvart et al. 2019 restriction; existential regular-constrained equations | automata reduction, cap/power equation, PSPACE existential backend | first-to-last source deletion; terminal prefix-free target capture; derived-automaton single-source class | show noncontainment from 1999/2019 source restrictions using realized examples; independently review proof and PSPACE formula size | “A decision procedure for the single-flagged-source terminal BorderAvoid class, using a one-visit normalization and constrained word equations.” |
| C069: composite-number witness-length support/nonsemilinear support | P-automata/cap languages already non-context-free; pattern/backreference and arithmetic word-language literature | repeated blocks and nonregular length behavior | exact fixed 11-state, three-flag terminal instance with composite-index support and divisor-count multiplicity | search explicit automata-language results with composite length sets; verify what “first” could mean in the flagged-border model | “An explicit terminal flagged-border instance with exactly characterized nonsemilinear witness lengths.” |
| C077: complete target-column decision and `k^2+k-2` witness bound | regular-language border algorithms with quadratic shortest witnesses; cap automata; Breuvart restriction | borders in automata, quadraticity, periodic tails | state-dependent ordered forbidden pairs; last occurrence of a target; terminal accepting-tail dichotomy; native finite pattern avoidance | source-level comparison with 2019 restriction; theorem-by-theorem comparison with bordered/unbordered NFA bounds | “A quadratic witness bound and decision method for the complete target-column terminal flagged-border class.” Avoid “first quadratic border bound.” |
| C078: sparse coloring certificate | finite congruences, automata color refinement, simulations | finite abstraction and state coloring | two-stage certificate that completion of target columns preserves all and only relevant last-aligned violations without increasing state count | broader search for relation-preserving completion/coloring theorems; prove exact novelty of certificate, not generic coloring | “A checkable sufficient certificate reducing certain sparse flagged instances to C077.” |
| C080: rank-query preimage closure and unrestricted decision candidate | N&P cap automata; word equations; graph-query boundedness/finite expansion; inverse-transduction ideas | automata graphs, regular-path queries, finite compilation, shared-word equations | same-grammar preimage under exact first-return KMP graph surgery; one shared generator per physical interval; whole-conjunction preservation; iterability with explicit weight bound | complete Lean stage 4b, weight bound and semantic transfer; human referee; exhaustive search for graph-transduction/CRPQ theorem; compare Schubert's failed invariant | “A candidate uniform preimage construction for conjunctive regular-path queries over first-return prefix-graph extensions.” Do not call it a decision theorem yet. |
| Full Problem 1.7 decision | open lineage; Schubert withdrawn; 2019 still presents NSSE as open | exact historical problem family, though semantic top-free transfer differs | total decision for bottom + covariant binary product over arbitrary trees, if C080 and bridge close | correctness, source-level equivalence, human review, exhaustive novelty check | “Would resolve the stated top-free arbitrary-tree problem if all recorded candidate obligations are discharged.” |

## Claims to avoid

- “First use of word equations/powers/borders in NSSE.”
- “First nonregular or non-context-free NSSE witness language.”
- “First quadratic shortest-border bound for automata.”
- “The full first-order theory result proves Horn entailment undecidable.”
- “The 1999 no-constants-in-constraints fragment is the same as semantic top-free Problem 1.7.”
- “Schubert solved NSSE in PSPACE.”
- “No prior theorem exists” based only on the bounded search.
- “C080 is essentially finished” before forward coverage, repeated-closure bounds, semantic composition and independent review.

## Highest-value separation artifacts

1. A normalized top-free constraint whose derived instance is C067 but which violates the 1999 and 2019 syntactic restrictions, or a proof that such realization is impossible.
2. The same for one nontrivial C077/C078 example with recurrent sources and targets.
3. A line-by-line comparison of Schubert Lemma 5.5 with C080's forward/reverse closure quantifiers.
4. A theorem search for CRPQ inverse images under graph interpretations that either supplies a reusable theorem or documents the exact mismatch.

# Prior-work repository for Problem 1.7

**Audit date:** 2026-09-18  
**Coordination:** issue #36  
**Status:** literature and translation audit only. It proves neither novelty nor correctness of any Subtail claim.

## Purpose

This directory is the canonical prior-work map for the semantic top-free problem in `research/problem.md` and for candidate contributions C067, C069, C077, C078 and C080. It separates four questions that are easily conflated:

1. What theorem did the source actually prove?
2. What signature, syntax, tree domain and logical fragment did it use?
3. Does that theorem transfer to Subtail's `{bottom, product}` arbitrary-tree model?
4. What novelty wording remains safe after the comparison?

## Reading order

- [Core NSSE lineage](nsse-lineage.md): Henglein–Rehof; Niehren–Priesnitz 1999 and 2003; Su et al.; Breuvart–Penelle–Rehof; Schubert.
- [Adjacent machinery](adjacent-machinery.md): regular-language borders, constrained word equations, backreferences, factorization forests and regular-path queries.
- [Claim-by-claim novelty matrix](novelty-matrix.md): closest known result, overlap, difference and open verification obligation.
- [Bibliography and source status](bibliography.md): stable URLs, publication status and source-quality notes.

The older [bounded literature check](../literature-check.md) remains a compact entry point. This directory supersedes it for depth, not for claim status.

## Mandatory comparison dimensions

| Dimension | Values that must be stated |
|---|---|
| Semantic signature | `{bottom, product}`, `{bottom, top, product}`, other |
| Constraint syntax | whether constants occur in hypotheses; simple/flattened equations; conclusion form |
| Tree domain | finite, regular/rational, arbitrary possibly infinite |
| Logic | Horn entailment, full first-order theory, language universality, existential equations |
| Result status | peer-reviewed theorem, workshop slides, preprint, withdrawn preprint |
| Transfer | direct, conditional on a proved encoding, analogy only, or inapplicable |
| Subtail overlap | C067, C069, C077, C078, C080, semantic bridge |
| Residual obligation | explicit theorem or separation example still needed |

## Current bottom line

- The historical NSSE literature already contains automata/cap translations, word equations, powers and nonregular cap languages. Those ideas alone are not novel.
- The 2019 Breuvart–Penelle–Rehof slides add a relevant 2-EXPTIME syntactic restriction and must be compared explicitly with C067/C077.
- Ordinary border detection for regular languages already has algorithmic and quadratic-witness results. C077's possible novelty is the state-labelled forbidden-pair condition and terminal last-target collapse, not quadraticity by itself.
- Schubert's 2021 PSPACE claim is withdrawn because an error in Lemma 5.5 invalidates the subsequent construction. It is prior attempted work, not an established upper bound.
- No inspected source supplies C080's exact uniform preimage closure for a whole conjunction over one shared first-return generator. This is a bounded-search conclusion, not proof of priority.

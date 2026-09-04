# Problem and notation

**Goal:** decide Problem 1.7 of [the August 31 memo](../papers/sep-topfree.pdf). No general decision procedure is established in this repository.

Given a finite constraint set C and variables alpha, beta, decide whether every type assignment satisfying C also satisfies alpha <= beta.

## Scope

- Constructors: bottom and one covariant binary product. Top is absent as a constructor.
- Types: arbitrary, possibly infinite trees. The infinite full binary tree remains a greatest element.
- A product-node set X(t) represents a type; these sets are prefix-closed. Subtyping is set inclusion.
- Countermodels can be regular infinite trees under the memo's characterization. This does not equate the problem with finite-tree entailment.

## Shared notation

| Symbol | Meaning |
|---|---|
| C | A finite normalized subtype-constraint set |
| W | Pushdown system propagating product-node membership |
| S, F, B | The three conditions in Theorem 2.6: seed safety, forced-fact exclusion, and separation from seeded prefixes |
| pi | A finite candidate witness word |
| c(i) | DFA state after the first i letters of pi |
| G | Ordered relation of forbidden endpoint-state pairs |
| lrs(pi) | Longest suffix occurring earlier; the implementation uses 0 when none exists |
| L, D | Bounds on border length and induced period, respectively |
| N''(L,D) | Necessary finite-state condition; emptiness certifies NO |
| S''(L,D) | Sufficient finite-state condition; nonemptiness yields a witness |
| B(I) | Minimum L+D with a successful sufficient condition for instance I |

The overloaded B symbols have different roles: condition B in Theorem 2.6 is not the budget B(I).

## Known dependency chain

Top-free non-entailment reduces to prefix-reach avoidance with regular side conditions, then to flagged-border avoidance. A decision procedure for the latter would solve the former. The full converse preserving arbitrary regular side conditions has not been supplied.

Use [the claims ledger](claims.md) for exact statements and evidence, [the research tracker](README.md) for execution status, and [the initial review](../REVIEW.md) for the detailed derivations.

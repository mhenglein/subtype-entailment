# Problem and notation

**Result:** [C081](claims.md#c081) gives a Lean-checked executable decision for Problem 1.7 of [the August 31 memo](../papers/sep-topfree.pdf). The exact scope and semantic contract remain below.

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

Finite expression constraints and queries normalize with exact model extension
and restriction. Normalized non-entailment is equivalent to an original witness
in an effectively constructed absorbing summary instance. C031 splits witness
existence into the C029 infinite-continuation branch and a terminal branch;
both now have checked total Booleans. Their negated disjunction, followed by
normalization, gives the unconditional C081 entailment theorem.

The formal input is a finite list over `Expr (Fin n)`. A finite named constraint
set and variable query embed by choosing finite variable indices and listing
the constraints; repetitions do not change their universal interpretation.
This is an effective input encoding, not a theorem about a text/JSON parser.
The tree semantics use arbitrary prefix-closed product-node sets and retain
the memo's bottom/product domain. [Independent final semantic readback](../notes/2026-09-19-entailment-decision-independent-readback.md).
The full converse preserving arbitrary abstract BorderAvoid annotations is a
separate statement and is not assumed by this solution.

Use [the claims ledger](claims.md) for exact statements and evidence, [the research tracker](README.md) for execution status, and [the initial review](../REVIEW.md) for the detailed derivations.

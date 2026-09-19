# Bounded literature check: Problem 1.7

The maintained entry point is now the [prior-work repository](prior-work/README.md): [bibliography](prior-work/bibliography.md), [core lineage](prior-work/nsse-lineage.md), [failure modes](prior-work/failure-modes.md), [novelty/transfer matrix](prior-work/novelty-matrix.md), [coverage](prior-work/search-log.md), and [agent handoff](prior-work/agent-handoff.md).

This remains a bounded literature audit, not a completeness or priority certificate. It concerns the exact semantic top-free arbitrary-tree problem in [research/problem.md](../research/problem.md). The full historical NSSE signature, a syntactic no-constants restriction, and this semantic universe are not interchangeable without proof.

## Results and non-implications retained from the earlier audit

| Source key | Useful content | Limit |
|---|---|---|
| PW-HR98 | Historical non-structural PSPACE-hardness construction | Ambient-top uses require a top-free simulation or fresh reduction. |
| PW-NP99 | Decidable restricted syntax over bottom/top/product semantics | No top in constraints does not remove top from valuations. |
| PW-NP03 | Cap-set/word-equation characterization and unary case | Shared powers and hidden equations are established prior art, not a solution of this target. |
| PW-SU06 | Full first-order undecidability | Does not imply Horn entailment undecidability. |
| PW-BPR19 | Later product-only restriction announced in slides | Full archival proof and class-transfer comparison remain open. |
| PW-SCH21 | Withdrawn attempted PSPACE solution | Use v1 to inspect the failed extension claim; use v2 for status. No valid upper bound follows from the withdrawn proof. |
| PW-BLLS25 | Prefix/period saturation methods for families of automata | A transfer preserving finite-cut endpoint relation G is unproved. |
| PW-TLCA14 / PW-DOL16 | Historical descriptions of the research problem | Their dates are not evidence for exhaustive 2026 status. |

All keys, stable primary links and inspection levels resolve in [the bibliography](prior-work/bibliography.md). Previously recorded theorem checks are labeled historical rather than presented as fresh complete proof audits.

## Corrections and new preservation

The 1997 *The Complexity of Subtype Entailment for Simple Types* and 1998 *Constraint Automata and the Complexity of Recursive Subtype Entailment* are distinct Henglein–Rehof papers. The ICALP DOI belongs to the latter. Su et al.'s journal publication is TOPLAS 2006, extending POPL 2002; `fot_04.pdf` is a manuscript filename. Schubert v1 was submitted in September 2021 and v2 withdrawn in December 2021. A full-signature result would require a proved transfer to settle the top-free model; lack of that transfer is not a proof that transfer is impossible.

The initial September 18 'deep audit' was primarily consolidation and was reopened in issue #36. Subsequent discoveries now preserved in files include the [Priesnitz split-lemma counterexample](prior-work/dossiers/priesnitz-2004.md), the [exact Schubert extension obligation](prior-work/dossiers/schubert-2021.md), and [specialist-journal boundaries](prior-work/dossiers/specialist-boundaries.md). The MFCS 2025 negated-containment and ICALP 2026 backreference papers were already in older Subtail notes; they are centralized, not claimed as new finds.

## Next research use

Before borrowing a theorem, record source version, exact hypotheses, quantifiers, representation size and an effective mapping to Subtail. Before claiming a new decidable subtype fragment, establish the necessary source-level relationship to the derived automaton. Before claiming no relevant source exists, consult the explicit [unsearched and unresolved obligations](prior-work/open-obligations.md).

The historical note remains available in Git at the consolidation base `df222241dc1a55ac6ee5da3cba3aedf662b3e285`. No scientific claim is promoted by this navigation and citation correction.

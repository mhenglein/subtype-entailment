# Novelty and transfer matrix

This table specifies claims to compare, not novelty scores. A theorem not found in this bounded search is **not** thereby absent from the literature. Source keys resolve in [bibliography.md](bibliography.md); scientific status resolves in the current [claims ledger](../../research/claims.md).

| Claim | Closest comparison | Possible distinguishing statement | Required evidence before a novelty claim |
|---|---|---|---|
| C067: single-source terminal BorderAvoid | PW-NP99, PW-NP03, PW-PRI04, PW-BPR19; existential equations | One-visit normalization and terminal prefix-free capture for the stated derived-automaton class | Review the actual capture/formula-size proof; compare to repaired or alternative thesis arguments; prove the relevant source-level encoding/non-subsumption. |
| C069: nonsemilinear witness-length support | Cap/P-automata nonregularity, periodic-word and pattern-language literature | An exact fixed terminal flagged instance with characterized support and multiplicity | Check equivalent examples under other terminology. Nonregularity/non-context-freeness alone is old; nonsemilinearity does not refute decidability or a computable shortest-witness bound. |
| C077: complete target columns; quadratic certified-class bound | PW-BORD09, including its linear ordinary-unbordered bound; PW-BPR19; PW-HHL25 | State-labeled forbidden comparisons, last-target normalization and the exact class/bound | Preserve colors under shortening; distinguish the native algorithm from a backend import; compare source-level restrictions, not the adjective 'quadratic'. |
| C078: sparse completion certificate | Automata congruences/color refinement; C077 | A checkable sufficient certificate that column completion preserves the relevant bad language without state/length increase | Prove the claimed preservation; compare relation-sensitive completion literature. Failure of this certificate is UNKNOWN, not NO or proof that no other certificate exists. |
| C079: source-sensitive target-return elimination | C077/C078; PW-HHL25; synchronized-return methods | Certified transport to last original targets with legal repeats and state projection | Review the return/projection hypotheses and recursive product semantics; do not replace several synchronized conditions by independent single-predicate solvers. |
| C080: rank-query closure candidate | PW-NP03; PW-BFR19; PW-SCH21; finite-algebra tools | Same-grammar, whole-conjunction preimage under the exact directed first-return graph extension, with shared generators and effective iteration | Current ledger obligations, especially forward coverage, remaining size/finishing and semantic composition; independent human review; exact graph-transduction prior-art comparison. No decision-theorem promotion here. |
| Problem 1.7 itself | Historical full-signature NSSE lineage; withdrawn attempted solution | A total decision for the stated top-free arbitrary-tree model, if all dependencies close | Prove the full reduction and bound, with exact semantic domain. Distinguish this target from a claimed resolution of every historical NSSE variant. |

## Two corrections to the earlier comparison method

**Syntactic violation is not enough.** An input using syntax excluded by an old theorem may admit an equivalent encoding inside its decidable class. A separating example is a useful lead, not a non-subsumption proof. Compare normalizations, admissible encodings and semantic domains explicitly.

**Automaton-level novelty is not automatically subtype-level novelty.** The repository records a forward reduction to flagged-border avoidance; a general converse with arbitrary regular side conditions has not been supplied. A new result for a class of flagged automata must either be presented at that level or accompanied by the precise realization/transfer theorem needed for the subtype claim.

## Safe wording

Describe the exact class, algorithm or obstruction and its evidence level. Avoid 'first use of word equations in NSSE', 'first nonregular cap language', 'first quadratic automata-border bound', 'Schubert's PSPACE theorem', 'general word equations decide this', and 'no previous result exists'. The local thesis finding refutes a literal lemma, not all prior decidability work.

The unresolved obligations are [O01–O10](open-obligations.md). Closing a documentation issue, passing CI, or receiving agreement from another agent does not establish mathematical correctness or publication priority.

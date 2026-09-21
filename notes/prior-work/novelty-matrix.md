# Novelty and transfer matrix

## September 21 frozen-candidate comparison

The [fresh bounded comparison](publication-comparison-2026-09-21.md) checks the
primary Henglein–Rehof statements and adds NP03 Section 4 Proposition 1 as the
explicit dual-safety precedent for C088. The manuscript now separates its four
contributions and their formalization boundaries. No general priority claim or
exhaustive search follows. C089–C091 are companion results with separate ordinary
proofs and review; they do not expand the frozen paper's scope.

This table specifies claims to compare, not novelty scores. A theorem not found in this bounded search is **not** thereby absent from the literature. Source keys resolve in [bibliography.md](bibliography.md); scientific status resolves in the current [claims ledger](../../research/claims.md). The [agent handoff](agent-handoff.md) points to current authority; historical pauses and task lists are not current instructions. The [dated detailed review](review-2026-09-19.md) supplies source-to-obligation reading routes.

**September 20 acceptance pass.** The [publication review](../2026-09-20-publication-acceptance.md)
records fresh primary-source locators and bounded citation/search coverage.
The paper now explicitly credits NP03 Corollaries 1 and 3: unary decidability
and reductions between finite, regular and arbitrary tree decision problems.
Those reductions do not assert identical answers for the same unmodified
input in every domain. Henglein–Rehof's structural and nonstructural results
remain the leading historical comparison. The author-hosted SANPT manuscript
title and source status are corrected; the official SCH21 withdrawal is
reconfirmed. No stronger full-input complexity, non-subsumption, or priority
claim is established by this review.

**September 20 refinement.** The C081 fragment whose premises and query contain
no bottom constants reduces in polynomial time to NP99's restricted
arbitrary-tree problem: name products, add `omega=omega×omega`, and guard each
name by `z<=omega`. The equation forces the full product tree and the guards
exclude top labels. Both model-transfer directions are proved and independently
reviewed in the [extension study](../2026-09-19-post-c081-extensions.md).
NP99 Theorem 14 therefore supplies a PSPACE upper bound for this fragment;
its decidability is inherited, not a candidate novelty. This does not cover
bottom/denial constraints, finite-tree semantics or lower-bound transfer.
Identity translation alone fails even on constant-free syntax. The full C081
comparison and exact terminal-compiler comparison below remain open.

## September 20 hardness and explicit-top transfer

The [integration review](../2026-09-20-hardness-top-integration.md) incorporates
the accepted #70/#71 arguments into paper Sections 12.3 and 14. This changes
the mathematical transfer status, not the bounded literature-search coverage
or publication-priority status recorded by the earlier reviews.

| Claim | Inherited contribution | New argument supplied here | Still uncertain or outside scope |
|---|---|---|---|
| C087, paper Theorem 12.3 | Henglein–Rehof 1998 Section 4: PSPACE-complete binary all-accepting NFA universality, constraint-automaton hardness method; their Theorems 1/2 concern a richer valuation domain | Logspace bottom/product marker context H(X,Y)=(X×Y)×bottom; all target valuations in the positive direction; simultaneous regular missing-word countermodel; n+2 variables and m+1 always-satisfiable premises | Ordinary proof, not Lean complexity theorem. No finite-tree transfer, PSPACE membership or priority claim. Every produced input forces an infinite reference. |
| C088, paper Theorem 14.4 | C081 top-free decision; earlier constraint/word-language lineage, including Henglein–Rehof and Niehren–Priesnitz | Exact labelled-tree/covering-language correspondence; dual projections and universal lifting under opposite SAT; full arbitrary-tree top decision in at most four C081 calls | Language core checked only; full expression compiler/composition ordinary. Exact comparison of this lifting construction with all prior encodings remains a literature task. No new finite/regular-top, arity or variance theorem. |

The HR98 primary-PDF gate in the submission review reads published pages
621–623: binary CLOSED-UNIV hardness, the original top-valued countermodel,
and the separate finite truncation. The latter is explicitly not imported
into C087. The existing guarded NP99 transfer still gives a PSPACE upper bound
only for constant-free top-free syntax. The two results do not combine into
PSPACE completeness, since their input fragments differ.

## September 20 standalone-paper comparison

The [manuscript](../../paper/manuscript.md) now integrates this lineage in
Sections 1.1, 2 and 12. The fresh bounded primary-source review is recorded in
[the rewrite readback](../2026-09-20-paper-rewrite-readback.md). The following
are inherited results, not claims of a C081 complexity classification:

| Source and exact locator | Domain and result | Transfer limit |
|---|---|---|
| Henglein–Rehof 1997, Theorems 4.7–4.8, Corollary 4.9 | Structural finite simple types over a nontrivial base lattice; coNP completeness, hardness already with a covariant binary constructor | Different order and tree domain. |
| Henglein–Rehof 1998, Section 4 (Theorem 1), Section 4.1 (Theorem 2) | Constraint automata and PSPACE hardness for nonstructural finite and possibly infinite trees; ambient signature includes bottom, explicit top, product and arrow | The original product-based reduction does not itself restrict valuations to C081; C087 supplies a different arbitrary/regular bottom-product transfer, not the finite one. |
| Henglein–Rehof 1998, Theorem 5 | PSPACE completeness for structural infinite trees over a lattice of constants | Distinct from their nonstructural hardness result and from C081. |
| Niehren–Priesnitz 1999, Theorem 14 | P-automata; PSPACE completeness for product equations and variable inequalities over finite or possibly infinite bottom/product/top values | The guarded constant-free transfer supplies one upper-bound direction; bottom literals and denials are not covered. |
| Niehren–Priesnitz 2003, Theorems 1, 2, 4 and Lemma 1 | Cap-automata universality and shared-word characterization for one covariant constructor with bottom/top, distinguishing finite, regular and arbitrary trees | A characterization is not a general decision theorem or an automatic top-free transfer. |

The paper's Proposition 12.2 also gives the existing ordinary effective
regular-countermodel proof in full. It is not a new regular-model existence
claim or a checked NFA-to-tree extractor. Finite-tree answers and explicit-top
answers remain separate. The exact whole-conjunction preimage comparison and
theorem priority remain unresolved by this bounded review. The separate C088
proof now supplies the stated explicit-top reduction. No
publication-priority claim follows from failure to find a matching theorem.

## September 20 finite-tree paper comparison

[C085](../../research/claims.md#c085) now has its own theorem and full proof in
manuscript Sections 1.3 and 13. The [dated finite review](finite-tree-comparison-2026-09-20.md)
compares HR97 Theorems 4.7–4.8/Corollary 4.9, HR98 Theorem 2, NP99 Theorem 14,
and NP03 Theorems 1, 2, 4/Lemma 1 against the exact finite bottom/product domain.
NP99 treats both finite and arbitrary valuations, with top still present in
the values. NP03 allows one covariant constructor of arity at least one.
The HR98 author PDF was read for this review; the old C081 access limitation
is historical. The finite consuming-cycle proof and its checked implementation
are established in the ledger; their novelty and any PSPACE transfer are not.

| Claim | Closest comparison | Possible distinguishing statement | Required evidence before a novelty claim |
|---|---|---|---|
| C067: single-source terminal BorderAvoid | PW-NP99, PW-NP03, PW-PRI04, PW-BPR19; existential equations | One-visit normalization and terminal prefix-free capture for the stated derived-automaton class | Review the actual capture/formula-size proof; compare to repaired or alternative thesis arguments; prove the relevant source-level encoding/non-subsumption. |
| C069: nonsemilinear witness-length support | Cap/P-automata nonregularity, periodic-word and pattern-language literature | An exact fixed terminal flagged instance with characterized support and multiplicity | Check equivalent examples under other terminology. Nonregularity/non-context-freeness alone is old; nonsemilinearity does not refute decidability or a computable shortest-witness bound. |
| C077: complete target columns; quadratic certified-class bound | PW-BORD09, including its linear ordinary-unbordered bound; PW-BPR19; PW-HHL25 | State-labeled forbidden comparisons, last-target normalization and the exact class/bound | Preserve colors under shortening; distinguish the native algorithm from a backend import; compare source-level restrictions, not the adjective 'quadratic'. |
| C078: sparse completion certificate | Automata congruences/color refinement; C077 | A checkable sufficient certificate that column completion preserves the relevant bad language without state/length increase | Prove the claimed preservation; compare relation-sensitive completion literature. Failure of this certificate is UNKNOWN, not NO or proof that no other certificate exists. |
| C079: source-sensitive target-return elimination | C077/C078; PW-HHL25; synchronized-return methods | Certified transport to last original targets with legal repeats and state projection | Review the return/projection hypotheses and recursive product semantics; do not replace several synchronized conditions by independent single-predicate solvers. |
| C080: rank-query closure candidate | PW-NP03; PW-BFR19; PW-SCH21; finite-algebra tools | Same-grammar, whole-conjunction preimage under the exact directed first-return graph extension, with shared generators and effective iteration | Read the current ledger for discharged semantic/compiler subclaims. Compare the exact graph-preimage result with prior art; distinguish quantitative U/F claims and final subtype composition from the checked terminal decision. No promotion by this matrix. |
| C081: complete finite-expression decision | PW-NP99; PW-NP03; PW-PRI04; PW-BPR19; PW-SCH21 | A total executable Boolean and kernel-checked correctness theorem for finite syntax over bottom and one covariant binary product, with arbitrary prefix-closed product-node valuations, including nonregular infinite trees; the checked summary/infinite/terminal composition is part of the candidate contribution | Candidate new relative to the inspected sources, not a priority claim. The exact no-top and bottom/top domains are distinct; C088 now supplies an ordinary decision reduction from the latter. Compare its two projections and universal lifting with prior encodings. Compare the terminal first-return/rank-query compiler with cap universality and periodic-selection results. Preserve the withdrawn status of SCH21 and slide-only status of BPR19. Keep complexity, finite-tree restrictions, and C080 U/F claims separate. See [dated C081 review](c081-review-2026-09-19.md). |
| C085: complete finite-tree decision | HR97 Theorems 4.7–4.8/Corollary 4.9; HR98 Theorem 2; NP99 Theorem 14; NP03 Theorems 1, 2, 4/Lemma 1 | A consuming reverse-pop cycle rules out finite models; otherwise finite-seed canonical countermodels are finite. A total checked Boolean decides the original expressions over finite bottom/product valuations. | Compare the forced-target hypothesis and both model-transfer directions with the older finite results. Structural simple-type results use a different order; nonstructural comparisons allow semantic top. The infinite omega guard cannot transfer a finite upper bound. Other encodings, exact non-subsumption and priority remain open. See [dated finite review](finite-tree-comparison-2026-09-20.md). |
| C087: exact PSPACE lower bound | HR98 Section 4 and Theorem 1 | Marker coding transfers binary CLOSED-UNIV into always-satisfiable arbitrary/regular bottom-product inputs | The ordinary proof and source audit establish transfer. Priority, tight complexity and a finite-domain lower bound remain separate. |
| C088: explicit-top arbitrary-tree decision | HR98; NP99; NP03 Section 4 Proposition 1; C081 | Two compatible projections and least forced-top language reduce all finite expressions to at most four top-free calls | The ordinary theorem is reviewed and the language core checked. Compare exact lifting/compilation statements before claiming novelty; no full Lean expression endpoint yet. |
| Problem 1.7 itself | Historical full-signature NSSE lineage; withdrawn attempted solution | C081 supplies the total checked decision for the exact top-free arbitrary-tree model | Compare the complete construction and semantic domain with prior work. Keep explicit numerical bounds, complexity classification and other NSSE signatures separate. The result is established in the current ledger; novelty remains a comparison question. |

## Two corrections to the earlier comparison method

**Syntactic violation is not enough.** An input using syntax excluded by an old theorem may admit an equivalent encoding inside its decidable class. A separating example is a useful lead, not a non-subsumption proof. Compare normalizations, admissible encodings and semantic domains explicitly.

**Automaton-level novelty is not automatically subtype-level novelty.** The repository records a forward reduction to flagged-border avoidance; a general converse with arbitrary regular side conditions has not been supplied. A new result for a class of flagged automata must either be presented at that level or accompanied by the precise realization/transfer theorem needed for the subtype claim.

## Safe wording

Describe the exact class, algorithm or obstruction and its evidence level. Avoid 'first use of word equations in NSSE', 'first nonregular cap language', 'first quadratic automata-border bound', 'Schubert's PSPACE theorem', 'general word equations decide this', and 'no previous result exists'. The local thesis finding refutes a literal lemma, not all prior decidability work.

The unresolved obligations are [O01–O10](open-obligations.md). Closing a documentation issue, passing CI, or receiving agreement from another agent does not establish mathematical correctness or publication priority.

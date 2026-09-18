# Core non-structural subtype-entailment lineage

**Method.** Statements below were checked against primary papers or the authors' slides and official records. “Relevance” is a transfer analysis, not a citation-count summary.

## Clinical comparison

| Source | Exact established or claimed result | Model and hypotheses | Mechanism | Relevance and non-implication |
|---|---|---|---|---|
| Henglein–Rehof, ICALP 1998 | PSPACE hardness for non-structural subtype entailment; the historical starting lower bound. | Full non-structural model used by that paper, with ambient top and bottom; finite and recursive/infinite variants are treated. | Reduction encoding automata computations in subtype constraints. | Does not automatically establish PSPACE hardness for the semantic top-free universe. A top-free simulation or fresh reduction is required. |
| Niehren–Priesnitz, 1999 | The restricted constraint language is PSPACE-complete for finite and possibly infinite trees (Theorem 14). | Ambient signature `{bottom, top, product}`; bottom/top remain semantic labels. The restriction excludes their syntactic occurrence in constraints. | Polynomial reduction to finite-automaton universality; P-automata explain why the unrestricted case can be nonregular. | Crucial prior art for decidable restrictions. It is not Problem 1.7: “constants absent from hypotheses” is not “top absent from the semantic type universe.” |
| Niehren–Priesnitz, TACS 2001 / I&C 2003 | NSSE for `{bottom,f,top}`, one covariant constructor, is equivalent to universality of restricted cap-set expressions; all arities at least two and finite/possibly-infinite variants are polynomially interreducible. Unary is decidable. | Full top/bottom semantics. The constraint language is normalized but expressive for the intended NSSE problem. | Cap automata and cap languages. Membership obeys `pi in S° iff exists mu,nu (mu in S and pi nu = mu pi)`, exposing positive forall-exists regular-constrained word equations. | Strongest conceptual ancestor. Shared powers, periodicity, borders and regular-constrained equations are not novel. It does not decide the binary case or directly transfer to semantic top-free Problem 1.7. |
| Su–Aiken–Niehren–Priesnitz–Treinen, 2002/2004 | The full first-order theory of non-structural subtyping with bottom and a binary constructor is undecidable for recursive/infinite trees (Theorem 3.10); unary-symbol theories are decidable (Theorem 5.10). | Full first-order formulas, including quantification and negation; strictly richer than Horn entailment. | PCP encoding for undecidability; tree-automata construction for the unary case. | Does not imply undecidability of positive Horn entailment or BorderAvoid. It is a boundary result and a warning against importing a richer logic. |
| Breuvart–Penelle–Rehof, 2019 slides | A 2-EXPTIME decidable restriction is announced for product-only simple equations when `bottom×bottom` and `top×top` do not occur; an alternative assumes equations identifying top and bottom with their homogeneous products. | Full top/bottom NSSE(×), simple equations, conclusion `x<=y`, with the stated syntactic restriction. Source located is a 17-page slide deck, not a peer-reviewed full proof. | Refines the cap-language universality form; reduces universality to finitely many ultimately periodic/Büchi checks using suffix-closed saturated regular language `K`. | Mandatory comparison for C067/C077. The restriction is syntactic on source constraints, whereas Subtail subclasses are defined on derived terminal automata. Neither inclusion direction is currently proved. Treat complexity/result as “announced in slides” until a full publication is located. |
| Schubert, arXiv:2109.02458 (2021) | Claimed PSPACE membership for finite and regular type expressions. The arXiv record explicitly says the paper was withdrawn because an error in Lemma 5.5 invalidates the further construction. | Full-signature NSSE rather than the semantic top-free fragment. The abstract's claim remains searchable, but is not an established theorem. | Proposed automata/normal-form construction downstream of Lemma 5.5. | Must be cited as a failed attempt. It neither settles Problem 1.7 nor supplies a valid upper bound. Any overlap with C080 must be checked at the failed lemma's exact invariant before asserting methodological independence. |

## Paper-by-paper notes

### Henglein and Rehof (1998)

- **Question:** complexity of structural and non-structural subtype-constraint entailment.
- **Contribution relevant here:** establishes the PSPACE lower-bound lineage and formulates the unresolved upper-bound problem.
- **Transfer hazard:** Subtail's type universe removes the explicit top constructor while retaining an infinite full binary tree as a greatest element in the path-set order. This is not syntactically or semantically identical to the historical `top` label.
- **Required audit:** isolate every use of the top label in the hardness construction and either simulate it top-free or record that the lower bound is untransferred.

### Niehren and Priesnitz (1999)

- **Theorem checked:** Theorem 14 states PSPACE-completeness for the restricted language over both finite and possibly infinite trees.
- **Exact restriction:** no syntactic constraints assigning variables to bottom or top; the ambient signature still contains both constants.
- **Important negative lesson:** P-automata accept non-context-free languages because the first special edge can choose an unbounded period. Nonregular witness phenomena therefore predate Subtail.
- **C067/C077 comparison:** these claims restrict the derived terminal flagged-border instance, not the source syntax. A publishable novelty argument needs explicit instances satisfying the Subtail restriction but not known to arise inside the 1999 fragment, ideally with source-level realizations.

### Niehren and Priesnitz (2003)

- **Theorem checked:** Theorem 1 gives equivalence with universality of restricted cap expressions; Corollary 2 equates arities ≥2 and finite/infinite variants in their full-signature setting; Corollary 5 decides unary.
- **Equation content:** cap membership is equivalent to `exists mu,nu: mu in S and pi nu = mu pi`.
- **Novelty exclusion:** “translation to word equations,” “shared repeated word,” “border/power phenomenon,” and “non-context-free witness language” are not safe standalone novelty claims.
- **Potential Subtail distinction:** terminal state-labelled forbidden ordered pairs, source/target recurrence structure, and C080's one-shared-extension query preimage are more specialized than cap universality as stated.

### Su et al. (2004)

- **Theorem checked:** binary + bottom suffices for undecidability of the full first-order theory over recursive/infinite trees.
- **Quantifier boundary:** the reduction uses a richer first-order language; positive Horn entailment remains separate.
- **Safe use:** cite as evidence that nearby richer logics are undecidable and that a reduction must preserve the exact fragment.
- **Unsafe use:** “binary non-structural subtyping is undecidable,” without the full-first-order qualifier.

### Breuvart, Penelle and Rehof (2019)

- **Source status:** author-hosted workshop/research-day slides; no DOI or archival full paper located in this pass.
- **Announced scope:** product-only simple equations; no hypothesis `u<=v`; conclusion `x<=y`; syntactic exclusion of `bottom×bottom` and `top×top`.
- **Announced bound:** 2-EXPTIME.
- **Mechanism:** a cap-language universality expression `sum_i(R_i S_i° + R_i^<=)+K`; suffix-closed/saturated `K`; constructive finite subsets of cap bases; reduction to Büchi universality.
- **Open comparison obligation:** build source constraints realizing C067 and C077 examples and test whether the forbidden homogeneous products can be eliminated. Automaton-level orthogonality is suggestive but insufficient.

### Schubert (2021, withdrawn)

- **Version status:** v2 dated 2021-12-20; arXiv withdrawal notice attributes invalidity of the subsequent construction to Lemma 5.5.
- **Evidence rule:** the abstract is not evidence for a PSPACE theorem once the record withdraws it.
- **Clinical conclusion:** record three layers separately: the problem formulation remains relevant; any definitions/lemmas before the fault may remain usable after checking; every downstream theorem is unsupported unless reproved independently.
- **C080 comparison requirement:** compare Lemma 5.5's failed preservation/normalization property with C080's shared-generator and whole-conjunction obligations. Similar vocabulary is not enough; the exact quantifiers and reconstructed object must be aligned.

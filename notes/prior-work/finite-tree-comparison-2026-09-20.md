# Finite-tree theorem: exact literature comparison

Date: 2026-09-20. C085, A010/A018; issue #59 under #37.
Status: bounded primary-source review; no publication-priority claim.
The theorem and evidence remain in [C085](../../research/claims.md#c085).
The ordinary presentation is in [manuscript Section 13](../../paper/manuscript.md#13-entailment-over-finite-trees).

## Statement being compared

For finite expressions over bottom and one covariant binary product, C085
decides entailment when all variables denote finite bottom/product trees.
For the normalized propagation system, finite entailment holds exactly when
there is a consuming reverse-pop cycle or arbitrary-tree entailment holds.
Every push target is a forced product root. This is why a consuming cycle
excludes finite models, and why the negative branch admits finite canonical
countermodels. These are the hypotheses to compare; a paper's use of the
phrase "finite subtype entailment" does not establish the same domain.

The executable endpoint and its finite normalization are checked in Lean at
`4159c58bd3ff683d837d23b3eb4c18eef82e8d4d`. The separate finite-satisfiability
corollary and the displayed seed-dependent `n+d` estimate are ordinary
consequences, not separate checked Boolean endpoints. See the
[proof readback](../2026-09-20-finite-tree-decision-readback.md) and
[paper correspondence](../../paper/lean-map.md).

## Primary statements

| Source and locator | Exact result and semantic boundary | What this supplies here |
|---|---|---|
| Henglein–Rehof, LICS 1997, Theorems 4.7–4.8 and Corollary 4.9, pp. 352–361 | Structural entailment for finite simple types over a nontrivial lattice of base constants is coNP-complete. The hardness result already uses one covariant binary constructor. | A central complexity landmark. Its structural order differs from bottom below arbitrary product shapes. It is not a classification of C085. |
| Henglein–Rehof, ICALP 1998, Theorem 1 p. 622; Theorem 2 p. 623 | Nonstructural infinite-tree and finite-tree entailment, respectively, are PSPACE-hard. The ambient model has bottom, explicit top, product and function. The reduction's product syntax does not remove top from valuations. | Theorem 2 is the closest finite-semantic hardness comparison. A transfer to C085's valuation domain is an unproved additional step. |
| Henglein–Rehof 1998, Theorem 5 p. 626, setup p. 618 | Structural infinite-tree entailment over a lattice of constants is PSPACE-complete. The theorem itself does not add a nontrivial-lattice qualifier. | Keep this separate from the nonstructural hardness theorems and from finite C085. |
| Niehren–Priesnitz, ASIAN 1999, Propositions 1 and 13; Theorem 14 | Entailment in the restricted product-equation/variable-inequality language is PSPACE-complete over both arbitrary and finite trees. The syntax excludes bottom/top literals; the valuation signature remains `{bottom, product, top}`. | The closest restricted finite benchmark. The infinite guard used in our constant-free arbitrary-tree reduction cannot transfer its finite upper bound. |
| Niehren–Priesnitz, Information and Computation 186(2), 2003, Section 2, Theorems 1, 2, 4 and Lemma 1 | One covariant constructor of positive arity with bottom and explicit top; finite, regular and arbitrary domains are distinguished. Restricted cap-set/cap-automata universality and the shared equation `pi nu = mu pi` characterize the problem. | Inherited automata and shared-word structure. This is not a general decision theorem, nor a proof of our top-free finite cycle criterion. |

Primary records and full sources:

- HR97: [LICS record](https://lics.siglog.org/archive/1997/HengleinRehof-Thecomplexityofsubt.html),
  [author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1997b.pdf),
  [DOI 10.1109/LICS.1997.614961](https://doi.org/10.1109/LICS.1997.614961).
- HR98: [publisher record](https://link.springer.com/chapter/10.1007/BFb0055089),
  [author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf).
- NP99: [author record and PDF](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:99.html),
  [publisher record](https://link.springer.com/chapter/10.1007/3-540-46674-6_22).
- NP03: [author record and PDF](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:02.html),
  [publisher record](https://www.sciencedirect.com/science/article/pii/S0890540103001408).

## Conclusions and remaining obligations

Constraint automata, the separation of structural and nonstructural orders,
and the distinction between finite and infinite valuations are inherited.
The paper credits Henglein–Rehof at the introduction, normalization route and
finite comparison. The exact C085 contribution presented is its forced-cycle
dichotomy, finite canonical replacement, and executable composition for the
bottom/product domain. No matching theorem was identified in these four
inspected papers; this observation does not prove non-subsumption or priority.

Neither identity translation nor the equation `omega=omega×omega` solves the
finite comparison: the former admits top-valued target models, while the
latter has no finite model. Another encoding could still work. Establishing
or excluding such encodings, tracing the wider subsequent literature, and
comparing the precise terminal preimage construction remain open.
No PSPACE upper or lower bound for the full C085 input follows from this review.

The [older C081 review](c081-review-2026-09-19.md) records that the HR98 PDF
was unavailable at that time. That access limitation is superseded for this
review: the author-hosted PDF above was retrieved and read, including the
finite hardness theorem. The older note is retained as provenance.

## Review coverage

The read-only literature reviewer checked the primary papers and reported
exact theorem numbers, signatures, tree domains and metadata in
[#59](https://github.com/mhenglein/subtail/issues/59#issuecomment-5747928334).
The parent reconciled that report with the manuscript and existing dossier.
This is bounded agent review, not human peer review or a complete forward
citation search. No source papers or earlier receipts were changed.

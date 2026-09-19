# Core NSSE lineage and exact transfer boundaries

Source identities, versions and inspection levels are in [the bibliography](bibliography.md). These are selected-theorem dossiers, not claims that every proof in every source was reverified. Source keys are stable across the [register](sources.json), [failure catalogue](failure-modes.md), and [open obligations](open-obligations.md).

## PW-HR97 / PW-HR98 — the complexity baseline

**Question:** structural versus non-structural subtype entailment, with distinct simple and recursive type settings. **Result relevant to this project:** the 1998 paper supplies the historical non-structural PSPACE-hardness lineage; the 1997 simple-type paper is a separate publication. **Mechanism to audit:** the hardness construction's use of the ambient top label. **Transfer status:** unproved for Problem 1.7 merely from this citation. Absence of constants in input equations is not absence of those constants from admissible valuations. A top-free simulation or fresh lower-bound construction is needed. Do not attach the 1997 title to the 1998 DOI.

## PW-NP99 — decidable syntactic restriction

**Locator:** Theorem 14 in the author-hosted paper. **Scope:** a restricted constraint syntax over an ambient bottom/top/product universe, treating finite and possibly infinite trees. **Result:** PSPACE-completeness for that restriction. **Mechanism:** finite-automaton universality for the restricted syntax; P-automata explain nonregular behavior outside it. **Transfer status:** no direct identification with semantic top-free entailment. **Comparison task:** characterize the image of this restriction under Subtail's actual reduction; do not infer that image from an automaton drawing or one syntactically nonconforming example.

## PW-NP03 — the cap/word-equation characterization

**Locators:** Theorem 1; Corollaries 2 and 5 in the cited author copy. **Result:** full-signature NSSE with one covariant constructor is characterized by universality of restricted cap-set expressions; the paper relates arities at least two and finite/infinite variants and treats unary constructors separately. **Core mechanism:** cap membership exposes a shared-word equation of the form `pi nu = mu pi` with regular restrictions. **Prior-art consequence:** automata, repeated words, powers and hidden word equations were already central to NSSE. **Transfer limit:** those equivalences have hypotheses; they neither prove top-free equivalence automatically nor discharge a uniform finite scheme bound. A broad forall-exists undecidability theorem is likewise not automatically about this restricted cap syntax.

## PW-PRI04 — the overlooked thesis fragment

**Locators:** Chapter 11, printed pp. 111–114; definition of straightness, Theorem 11.1, Lemmas 11.1–11.2. **Why relevant:** it attempts a further cap-language restriction reduced to existential word equations, making it a serious comparison for C067-style unique captures. **Audit result:** the literal uniqueness lemma has a concrete finite-language counterexample. The source, calculation, stronger sufficient hypothesis and precise limits are in the [thesis dossier](dossiers/priesnitz-2004.md). **Status:** local audit finding awaiting independent review; the chapter's final decidability theorem has not been refuted by this finding. Do not silently use the printed lemma or silently repair the whole theorem by replacing straightness with prefix-freeness.

## PW-SU06 — a neighboring undecidability boundary

**Version:** TOPLAS 2006 extends POPL 2002; the repository's older theorem numbers refer to the extended manuscript. **Locators:** manuscript Theorems 3.10 and 5.10. **Scope/result:** undecidability of the full first-order theory with a binary constructor and bottom; a unary-symbol decidability result is also given. **Transfer limit:** full first-order formulas allow logical operations unavailable in the Horn entailment target. This is neither an undecidability proof for Problem 1.7 nor permission to insert arbitrary negations into a reduction. Keep the exact logical fragment in every citation.

## PW-BPR19 — the later product-only restriction

**Source:** 17-page author slide deck, not a located archival proof. **Announced result:** a 2-EXPTIME product-only restriction excluding the homogeneous products `bottom x bottom` and `top x top`, in the stated simple-equation setting. **Mechanism indicated:** cap expressions, finite periodic selections and Büchi-style checks. **Transfer status:** an important prior-art risk for C067/C077/C079, but neither direction of inclusion with Subtail's derived-automaton classes is established. **Next evidence:** locate the full write-up or obtain an author clarification, then compare precise source syntax, ambient semantics and admissible encodings. A slide statement is not upgraded to a refereed theorem here.

## PW-SCH21 — withdrawn extension/pumping attempt

**Version:** v1 September 2021; v2 December 2021 withdrawal. **Locators:** Definition 11, Proposition 5.4, Lemma 5.5. **Important correction:** the relevant failed step is a coordinated extension of a solution substitution, not just a vaguely similar automata normal form. The [withdrawn-proof dossier](dossiers/schubert-2021.md) separates the claimed invariant from the later withdrawal and the still-missing concrete failure reconstruction. It provides no valid PSPACE upper bound. Its relationship to C080 is an audit question, not an established common flaw or proof of methodological independence.

## Shared source-comparison contract

For a claimed import or novelty distinction, supply all six items: (1) source version and theorem; (2) constructor signature and semantic tree domain; (3) permitted constraint syntax and quantifier prefix; (4) effective encoding with size bound; (5) both directions required by the intended use; (6) the conclusion actually obtained. A full-signature theorem might transfer through a suitable construction, but that construction must be proved, not presumed impossible or presumed automatic.

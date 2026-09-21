# Publication contribution comparison — 21 September 2026

Scope: final manuscript review under #79 and the publication-candidate-20260921
integrator lease in #37. Baseline: fed560c6682e5ac1e1661d5c60e595f948e768ba.
This refresh checks the exact existing comparisons and the strongest nearby
precedent. It is a bounded primary-source review, not a priority certificate.

## Results and manuscript changes

The manuscript now separates four contributions: whole-conjunction first-return
preimages and their decision composition; the finite consuming-cycle decision;
the exact-domain hardness transfer; and the explicit-top reduction. Formal
coverage remains explicit. C086 is a separately checked companion result; the
paper retains its finite-enumeration proof of a computable bound in Section 11.
The new arity, graph-only and function-only records are also companion research,
not silently added claims in the paper.

| Primary source freshly inspected | Exact comparison and disposition |
|---|---|
| [Henglein–Rehof 1997 author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1997b.pdf), Theorems 4.7–4.8 and Corollary 4.9 | Structural finite simple types over nontrivial lattices; coNP-completeness. The hardness already uses a binary covariant constructor. Retain leading credit and the structural/nonstructural distinction. |
| [Henglein–Rehof 1998 author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf), Section 4, Theorems 1–2 and 5 | CLOSED-UNIV and constraint automata supply the historical source. Nonstructural infinite/finite lower bounds and structural infinite PSPACE-completeness have different domains. C087 supplies its own top-free target proof; its infinite reference tree prevents a finite-domain transfer. |
| [Niehren–Priesnitz full paper](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf), Section 4, Proposition 1 | Dual left/right safety already uses inherited bottom/top observations. Added explicit credit in Section 1.1. The precise comparison target for C088 is universal lifting through two finite top-free systems, not duality alone. |
| [Niehren–Priesnitz 1999](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf), restricted grammar and Theorem 14 | Retain the finite/arbitrary distinction and semantic top, even when the grammar omits constants. The paper's constant-free arbitrary-tree transfer has its own guard. |
| [Breuvart–Penelle–Rehof slides](https://lipn.univ-paris13.fr/~breuvart/articles/NSSA_journee.pdf), periodic-selection slides | Read the announced restricted result and its stated qualifications. No full archival proof was obtained in this bounded refresh; do not upgrade the slide-only evidence. |
| [Schubert version history](https://arxiv.org/abs/2109.02458) | Reconfirmed withdrawal because the error in Lemma 5.5 affects the later construction. Search snippets repeating the old abstract are not valid proof evidence. |

Fetched author PDF hashes: HR97
`fbf15cfbb38311aa663065386f452f16c724b3dc38a535afb25b636b7bd47eba`;
HR98 `6da53bb92428595af33d2466e71a8436cd43c41d750f75f010e909780d795d39`.
Only provenance is committed; downloaded PDFs and extracted text remain ignored.
The preceding finite-domain and core-lineage reviews retain their detailed
source mappings and source-version distinctions.

## Forward and terminology search log

Two bounded search rounds used these literal queries:

- `"subtype entailment" "decidability" after:2021`
- `"subtype entailment" "projection" top`
- `"first-return" "regular path queries" preimage`
- `"Non-Structural Subtype Entailment" Breuvart Penelle Rehof paper`
- `"subtype entailment" "top" "bottom" "projection"`
- `"first-return" "preimage" automata graph query`

Recent crawling dates were not treated as publication dates. The primary
version-history and full older theorem statements above control the conclusions.
Two forward leads, DOI 10.1145/3704907 and DOI 10.1145/3776689, were identified,
but their publisher pages failed to open. Their full texts were NOT reviewed,
and no scientific conclusion is drawn from their snippets. They remain leads
for a specialist's wider citation review, not evidence of novelty or absence.

## What remains uncertain

The exact preimage construction may have an equivalent encoding in graph-query
or transduction literature. The dual-projection lifting statement also needs
comparison against any such alternative encodings. This review does not provide
an exhaustive forward-citation export, a venue-by-venue search, author contact
or human refereeing. The paper claims its exact proved results and inherited
methods; it does not claim that no prior equivalent result exists.

Next useful external review: give a domain expert the frozen paper, the exact
four contribution statements and the declaration map. Ask specifically about
whole-conjunction preimages, model lifting and same-input versus inter-domain
reductions. No invitation was sent by this work.

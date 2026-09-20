# Mathematical paper and proof artifact

[Read the manuscript](manuscript.md) or its [PDF](../output/pdf/subtail-paper.pdf).
The paper states the exact arbitrary-tree bottom/product theorem, gives the
complete terminal construction in Sections 5–9, and integrates the
Henglein–Rehof and Niehren–Priesnitz comparisons. Section 12 gives ordinary
proofs of a restricted PSPACE transfer and effective regular countermodels.

The manuscript contains the mathematical argument. This directory and the
research records contain source pins, audit history and reproduction details.
Author names and affiliations remain placeholders at the owner's request.
Licensing remains pending. A checked theorem and an agent readback do not
establish publication priority or human peer review.

## Read the proof and its correspondence

- [Declaration map](lean-map.md): seventeen numbered paper results and their
  exact checked definitions and declarations. Historical P-identifiers remain
  in `lean-map.json` only to interpret earlier reviews.
- [Dependency map](dependency-map.md): the mathematical route to the decision.
- [Import graph](imports.md): the larger source-module closure, which includes
  unused exploratory results and is not a theorem-dependency audit.
- [Current rewrite review](../notes/2026-09-20-paper-rewrite-readback.md): scope,
  findings, corrections and validation limits for the standalone manuscript.
- [Original exposition review](../notes/2026-09-19-post-c081-paper-readback.md):
  preserved evidence for the earlier manuscript and source checkpoint.

The seventeen mapped results retain mathematical source revision
`c946d86b9e65da2877e0df42c710abbdcb5a4037`. Their source bytes are compared
with that revision. Corollary 11.1 and Propositions 12.1–12.2 are ordinary
proofs, not new Lean declarations. See the [extension proof record](../notes/2026-09-19-post-c081-extensions.md)
for the earlier regular-model and guarded-fragment arguments.

The reference Boolean may enumerate closed relation tables. The separate
[proved cached solver](../notes/2026-09-20-fast-summary.md) uses finite
saturation and early certificates, with a correctness/equality theorem and
an unchanged complete fallback. Neither implementation coverage nor diagnostic
timeouts are premises of the paper's qualitative theorem.

## Reproduce the paper

```sh
python3 paper/check.py
python3 paper/build.py
```

The first command needs only Python. It checks declaration locations, exact
source identities, generated maps, literal worked examples, bibliography keys
and separation of internal research administration from the manuscript.
It does not build Lean or prove the prose correct.

The second command uses Pandoc 3.11 and Tectonic 0.17.0. Pandoc's citation
processor reads `references.bib` and the bundled numeric `references.csl`.
The output is `output/pdf/subtail-paper.pdf`, generated TeX and a manifest
containing the render revision, source hashes, tool versions and PDF hash.
A true `source_files_match_render_revision` means all listed source bytes
were committed at the recorded revision. The manifest does not claim a
mathematical review. Tectonic fetches and caches its TeX bundle on first use.
On macOS, the tested tools can be installed with `brew install pandoc tectonic`.

After a Lean build, execute the small checked example:

```sh
(cd lean && lake env lean --run ../paper/example.lean)
```

It prints `true` and `false` for a listed inequality and its reverse. The
negative case has a root countermodel. For full formal reproduction, use
`python3 scripts/check_lean.py` and the additional audits documented in the
[C081 completion record](../notes/2026-09-19-entailment-decision.md).
Those historical results apply to their recorded revisions; a new PDF build
does not repeat them.

## Remaining scientific and publication questions

The [publication plan](../research/PUBLICATION_PLAN.md) separates manuscript
review, complexity, performance and extension theorems. The exact full-input
PSPACE comparison, complete implemented countermodel extraction, explicit top
and other signatures are separate obligations. The old proposed quantitative
bounds retain their status in the claim ledger; no notation in this manuscript
silently changes them. Historical release tags and receipts are preserved.

# Mathematical paper and proof artifact

[Read the manuscript](manuscript.md) or its [PDF](../output/pdf/subtail-paper.pdf).
The paper states the exact arbitrary- and finite-tree bottom/product theorems, gives the
complete terminal construction in Sections 5–9, and integrates the
Henglein–Rehof and Niehren–Priesnitz comparisons. Section 12 gives ordinary
proofs of a restricted PSPACE upper transfer, effective regular countermodels
and full arbitrary/regular PSPACE hardness using Henglein–Rehof CLOSED-UNIV.
Section 13 proves the finite-tree decision through a consuming-cycle test,
an acyclic word bound and finite canonical replacements. Section 14 proves
the arbitrary-tree explicit-top extension through compatible dual projections.

The manuscript contains the mathematical argument. This directory and the
research records contain source pins, audit history and reproduction details.
Author names and affiliations remain placeholders at the owner's request.
Licensing remains pending. A checked theorem and an agent readback do not
establish publication priority or human peer review.

## Read the proof and its correspondence

- [Declaration map](lean-map.md): twenty-three numbered paper results and their
  exact checked definitions and declarations. Historical P-identifiers remain
  in `lean-map.json` only to interpret earlier reviews.
- [Dependency map](dependency-map.md): the mathematical route to the decision.
- [Import graph](imports.md): the larger source-module closure, which includes
  unused exploratory results and is not a theorem-dependency audit.
- [Finite-tree revision review](../notes/2026-09-20-finite-paper-readback.md):
  finite proof, exact literature comparison, source pins and render evidence.
- [Earlier rewrite review](../notes/2026-09-20-paper-rewrite-readback.md): scope,
  findings, corrections and validation limits for the standalone manuscript.
- [Original exposition review](../notes/2026-09-19-post-c081-paper-readback.md):
  preserved evidence for the earlier manuscript and source checkpoint.
- [Frozen-candidate review](../notes/2026-09-21-publication-candidate.md): whole-paper
  readback, exact contribution comparison, render and expanded reproduction.

The seventeen original mapped results retain mathematical source revision
`c946d86b9e65da2877e0df42c710abbdcb5a4037`. The four finite-tree results use
`4159c58bd3ff683d837d23b3eb4c18eef82e8d4d`. The two explicit-top language lemmas use
`0eff4818d990821fd1c08f704a2392f2d0047cf5`. Every linked source file is compared
byte for byte with its recorded revision. Theorem 1.2 maps directly to the
finite-expression Boolean theorem; Theorem 13.3 assembles its checked positive
and negative semantic branches. Corollaries 11.1/13.4, Propositions 12.1–12.2,
Theorem 12.3, Lemma 14.1 and Theorem 14.4
are ordinary proofs, not new Lean declarations. The explicit-top map links
arbitrary-language lifting/decomposition only: it does not certify the
labelled-tree representation, finite expression compiler or final composition. The numerical estimate (13.2)
is proved in the text; the semantic formalization uses an existential bound.
See the [finite proof readback](../notes/2026-09-20-finite-tree-decision-readback.md)
and [earlier extension proof record](../notes/2026-09-19-post-c081-extensions.md).

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

Build the optional finite entry point, then execute the small checked example:

```sh
(cd lean && lake build +Subtail.FiniteTreeDecision && lake env lean --run ../paper/example.lean)
```

It prints `true` and `false` for a listed inequality and its reverse, followed
by `false` and `true` for the same forced-spine query under arbitrary and finite
semantics. The first negative case has a root countermodel; the spine has no
finite model. The example uses the proved cached implementation. For full formal reproduction, use
`python3 scripts/check_lean.py` and the additional audits documented in the
[C081 completion record](../notes/2026-09-19-entailment-decision.md).
For the finite extension, also run `python3 scripts/check_finite_tree_decision.py`.
For the explicit-top language core and both new independent corpora, run
`python3 scripts/check_explicit_top.py`. This does not expose a native top solver.
Historical results apply to their recorded revisions; a new PDF build does not
repeat them. JSON handling, extraction and rooted graph finiteness retain the
external boundaries documented in the solver notes.

For one logged reproduction from a fresh Linux clone, put Python 3.13.14 and
Lean 4.33.1 on PATH and run:

```sh
python3 scripts/reproduce_release.py
```

The runner refuses an existing `lean/.lake`, a dirty checkout, or an existing
output directory. It builds the default library and optional normalization,
C030, finite, optimized and certificate modules explicitly, then runs their
checks and the paper example. It also checks C082/C086 quantitative modules,
C087's corpus, the C088 language core, the three accepted ordinary extension
corpora, and native strict/diagnostic cases. Native process-group RSS monitoring
requires Linux. The normalization audit is not a default-library
import. Logs and a source-pinned receipt are written to
`tmp/release-reproduction/`. This reuses the installed toolchain; it does not
claim a fresh operating-system/toolchain installation or every historical
experiment. A failed or capped strict step stops the run and remains in its
receipt. The separately labelled stress step permits UNKNOWN without counting
it as a mathematical answer. PDF/manifest/source hashes must agree with the
recorded committed render inputs.

The [September 20 clean reproduction](../notes/2026-09-20-clean-reproduction.md)
records the actual fresh-cache run, exact revision, the preserved initial
setup failure and the successful 18-step receipt. The
[publication acceptance record](../notes/2026-09-20-publication-acceptance.md)
separates mathematical review, source comparison and visual inspection.
The [September 21 candidate](../notes/2026-09-21-publication-candidate.md) refreshes
that review for the expanded paper and package. Its
[fresh receipt](../results/publication-reproduction-20260921.json) records the
actual outcome; historical checks are not relabelled as fresh evidence.

C086's original terminal witness bound is a checked companion result. Section 11
retains its finite-enumeration proof of a computable bound. It does not expound
the explicit numerical bounds of C082 or C086.
Likewise, the new fixed-arity, graph-only and function-only research notes are
separate from this manuscript's theorem and proof map.

## Remaining scientific and publication questions

The [publication plan](../research/PUBLICATION_PLAN.md) separates manuscript
review, complexity, performance and extension theorems. The exact full-input
complexity classification, formalization of the countermodel producer and
explicit-top expression compiler, and other signatures are separate obligations.
The PSPACE lower bound and ordinary arbitrary-tree explicit-top decision are
now established with their exact limits in the integration record. Complete ordinary extraction
and checked certificates are already implemented. The old proposed quantitative
bounds retain their status in the claim ledger; no notation in this manuscript
silently changes them. Historical release tags and receipts are preserved.

[Hardness/top integration and review](../notes/2026-09-20-hardness-top-integration.md)
records the new source pins, proof boundaries, fresh combined checks and render.

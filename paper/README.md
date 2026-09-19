# C081 paper and proof guide

[Read the ordinary manuscript](manuscript.md), including the full terminal
first-return/preimage proof in Sections 5–9. [Lean correspondence](lean-map.md)
and [proof dependency map](dependency-map.md) accompany it.

This is a research draft based on checked source
`c946d86b9e65da2877e0df42c710abbdcb5a4037`. Author names and affiliations are
placeholders at Marcus's request. Licensing is pending. Neither novelty nor
publication readiness follows from the existence of a checked theorem.

## Reproduce

```sh
python3 paper/check.py
python3 paper/build.py
```

The first command uses only Python and checks declaration locations, source
identities, generated maps and literal worked examples. It does not run Lean.
The second needs Pandoc 3.11 and Tectonic 0.17.0 (the versions used for this
checkpoint), and emits `output/pdf/subtail-paper.pdf` with a source manifest.
Tectonic fetches its TeX support bundle on first use and caches it. The build
also saves the generated TeX source. Formatting dependencies do not alter the
pinned Lean toolchain. Install them on macOS with `brew install pandoc tectonic`.

After the Lean build, run `(cd lean && lake env lean --run ../paper/example.lean)`
for a small actual call to the checked entailment Boolean. Its two outputs
are `true` and `false`; the latter has a root countermodel.

For mathematical verification, follow the exact commands and recorded revisions
in [the C081 completion record](../notes/2026-09-19-entailment-decision.md).
`python3 scripts/check_lean.py` runs the pinned build and kernel replay; the
branch-specific audits and regressions are listed there. Source-map checks and
PDF generation do not repeat those proofs.

The [programme](../research/POST_C081.md) tracks the separate novelty, complexity,
performance, extension and packaging tasks. The paper does not turn the former
C080 numerical bounds into established results. Earlier failed attempts remain
in their original records.

## Draft checkpoint verification, September 20

The 22-page PDF was rendered from committed paper sources at `e794362` with
Pandoc 3.11 and Tectonic 0.17.0. The manifest records the full source revision,
source hashes and PDF hash; `source_files_match_render_revision` is true.
All 22 rendered pages were visually inspected after the final contents-page
adjustment. No missing glyph, clipped equation, overlapping text or TeX warning
was found. This is layout validation, separate from the mathematical readback.

`paper/check.py` passes for all 17 mapped results and literal examples. The
small Lean example was freshly executed on wb-marcus, using the existing
compiled checkout at `a7c4fbc` after comparing every core Lean source byte with
the `c946d86` source. It printed `true` and `false` as stated above. Its temporary
input was removed. This reused build is not a fresh whole-library replay.

E053 saved-result replay, research navigation checks (13 tests), the prior-work
source checker, the 226-record literature index and its nine tests pass.
`CITATION.cff` validates against the official CFF 1.2.0 schema with author
placeholders and no license field. The coordinating [programme issue](https://github.com/mhenglein/subtail/issues/53)
records the publication head and remote CI results after publication; absent
or pending runs are not represented here as passes.

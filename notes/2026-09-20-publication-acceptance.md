# Manuscript and contribution acceptance review

Date: 2026-09-20. Session: `publication-sequence-20260920`.
Related: A010/A017/A018, C081/C085, [#64](https://github.com/mhenglein/subtail/issues/64).
Starting main: `b63a90443c3b71d086a340785e83751c441190fc`.
Paper source/render: `caef0bca056a997250a46a52bbeee1dd1c8c59f6`.

## Result and review boundaries

**PASS within the recorded acceptance scope:** source/literature readback,
example/declaration-map checks, fresh proof reproduction, final PDF inspection
and a separate read-only mathematical review are complete. No substantive gap
was found in the reviewed terminal or finite-tree arguments. Two clarity
suggestions were applied and independently read back before acceptance.

The author/integrator reviewed the ordinary argument and exact primary-source
statements. The `publication_proof_review` agent has a separate read-only
assignment covering the terminal construction, finite-tree argument and their
Lean semantics. Its [final readback](https://github.com/mhenglein/subtail/issues/64#issuecomment-5750475163)
is pinned to `5a43064`, which includes the final paper source `caef0bc`. It inherited the conversation and existing manuscript; this
is an independent review of the supplied argument, not a blind independent
discovery or external human peer review. No worker may alter a theorem to make
the review pass. No Lean definition or proof source changes in this episode.

The [acceptance receipt](../results/publication-acceptance.json) separates
review, rendering, source checks and formal reproduction. The
[clean reproduction record](2026-09-20-clean-reproduction.md) gives the fresh
Lean and executable evidence; its source revision is stated separately.

## Concrete corrections

1. Section 1.1 now credits Niehren–Priesnitz's unary decidability result and
   reductions between finite, regular and arbitrary tree decision problems.
   A reduction does not say that the same unmodified instance has the same
   answer in all three domains. The paper retains its concrete forced-infinite
   example to make that distinction visible.
2. Section 12.3 states the scope of the effective first-return elimination
   without claiming publication priority or impossibility of a different
   reduction to an earlier decidable fragment.
3. The Su–Aiken–Niehren–Priesnitz–Treinen title now matches the author-hosted
   journal manuscript, *The First-Order Theory of Subtype Constraints*. The
   author publication record supplies 2006; the available manuscript has
   placeholder volume information. No unverified volume, pages or DOI were
   invented. The bibliography identifies the retrieved manuscript status.
4. The reviewer requested a second explicit distinction between old matching
   cursors and fresh state labels in Section 7.5, and a statement that the
   finite growth return path may mix epsilon and letter edges in Section 13.1.
   Both additions preserve the definitions and received a final source readback.
5. The PDF renderer keeps numbered theorem openings with their statements
   and section introductions with their first displays. Theorem 1.1 and the
   recurrence starting Section 9 no longer split across pages at those points.

The manuscript has no issue IDs, workstream/claim IDs, TODOs, internal task
lists, host names or ownership notes. Author/affiliation placeholders remain
by the owner's explicit choice. The theorem map and operational evidence are
in companion repository documents, not inserted into the mathematical prose.

## Primary-source comparison refreshed

| Source inspected | Exact locator and comparison | Consequence here |
|---|---|---|
| [Henglein–Rehof 1997 author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1997b.pdf) | Theorems 4.7–4.8 and Corollary 4.9: structural finite simple types over a nontrivial lattice; coNP completeness, already hard with a covariant binary constructor | The manuscript leads its historical account with this result and keeps the structural order distinct. |
| [Henglein–Rehof 1998 author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf) | Theorems 1–2: nonstructural infinite/finite PSPACE hardness; Theorem 5: structural infinite PSPACE completeness | Product-based syntax does not remove top-valued assignments from a reduction. No full top-free PSPACE claim is inherited without a model transfer. |
| [Niehren–Priesnitz 1999](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf) | Restricted grammar and Theorem 14: product equations/variable inequalities, with bottom/product/top in the valuation domain, finite and arbitrary trees | The guarded constant-free reduction in Proposition 12.1 gives the stated inherited upper bound only. Bottom/denial inputs and finite omega guards remain outside it. |
| [Niehren–Priesnitz 2003](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf) | Theorems 1, 2, 4, Lemma 1, Corollaries 1 and 3; cap automata, shared-word characterization, unary decidability and domain reductions | Characterization and reductions are credited explicitly; they are not treated as a general top-free decision or identical-domain-answer theorem. |
| [Su et al. author record](https://www.ps.uni-saarland.de/Publications/details/fot:04.html) and [manuscript](https://www.ps.uni-saarland.de/Publications/documents/fot_04.pdf) | Richer first-order theory and constrained-tree-automata context; author-hosted journal manuscript | Different quantifiers prevent transferring first-order undecidability into this entailment fragment by title alone. Bibliographic precision remains limited to the verified author record. |
| [Breuvart–Penelle–Rehof 2019 slides](https://lipn.univ-paris13.fr/~breuvart/articles/NSSA_journee.pdf) | Periodic-selection/return conditions, especially the universality qualification on slides 13–14 | Slides are relevant comparison material, not a proof source for the whole-conjunction preimage. |
| [Schubert official arXiv record](https://arxiv.org/abs/2109.02458) | Withdrawal on 20 December 2021 due to the incorrectly formulated Lemma 5.5 | The withdrawn PSPACE claim is not used as a theorem. Search snippets were not treated as current authority. |

The locally inspected HR97 and HR98 PDF hashes are respectively
`fbf15cfbb38311aa663065386f452f16c724b3dc38a535afb25b636b7bd47eba`
and `6da53bb92428595af33d2466e71a8436cd43c41d750f75f010e909780d795d39`.
Source papers were not edited or added to the repository in this review.

The forward/backward pass followed citations and author publication records
from the constraint-automata and cap-automata papers to the richer-theory paper,
the later slides and the withdrawn attempt. Bounded searches also used the
exact paper titles, `non-structural subtype entailment` with dates after 2021,
and `subtype entailment` / `first-return`, including arXiv. No retrieved source
established an exact subsuming theorem for the present complete construction.
That is a search observation, not a non-subsumption or priority proof. This
pass does not claim a complete citation index, every thesis descendant, or
every equivalent theorem under different terminology.

The [comparison matrix](prior-work/novelty-matrix.md) retains the exact open
transfer questions. Parallel lower-bound and extension investigations remain
separate, unreviewed work until their own obligations are discharged.

## Exposition and formal correspondence

The mathematical target remains finite input expressions over bottom and one
covariant binary product, universally quantified over arbitrary prefix-closed
sets of product addresses. Finite trees have their own theorem. Inconsistent
premises entail every query. Regularity, computability of a valuation and a
given word-length bound are not assumptions of the arbitrary-tree theorem.

The central exposition explicitly gives:

- the finite query grammar and its finite-graph satisfaction test;
- product-simple observer paths and the bounded diagram carrier;
- global physical marks, coincident positions and distinct positions with
  equal matching cursors;
- old-core recolouring, first-entry, failure, mismatch and endpoint wrap edges;
- one generator product per physical interval, including repeated traversals
  and intervals observed by no path atom;
- separate coverage and reconstruction arguments for one common extension;
- zero-length paths, one-group self-loops, overlapping returns and empty
  finishing continuations;
- rank-bounded iteration, cycle continuation and the final normalization map.

The finite section identifies the forced target of a push, consuming
reverse-pop cycles, the uniform pop bound and the finite canonical replacement.
It keeps ordinary numerical consequences distinct from directly exported Lean
declarations. The map lists 21 mapped results and four ordinary consequences;
their roles do not change merely because a documentation checker passes.

## Validation and artifact

`python3 paper/check.py` passed the 21-result source map, four ordinary-result
records, bibliography and literal examples. The executable example was also
run in the clean reproduction and returned `true, false, false, true`.
No Lean build is claimed by `paper/check.py` itself.

`python3 paper/build.py` rendered the committed source with Pandoc/Tectonic.
The manifest reports `source_files_match_render_revision: true`. All 28 pages
were rendered as images and visually inspected after the layout change:
title/abstract, complete contents, theorem statements, tables, formulas,
section transitions and all ten reference entries. No clipping, overlap,
missing glyphs, undefined citations, or TeX overfull/underfull warnings were
found. After the two prose clarifications, pages 16–18 and 24 were inspected
again; the other 24 page images matched the inspected version byte for byte.
PDF SHA-256:
`45f318d83e1c4988d67629413a969944b5eb9f487b1ecfb8a0a3604ad05da2f7`.

## Independent review disposition

The reviewer read the manuscript end to end and checked Sections 3–13 in
particular. It inspected the concrete `RankQueryCoverage.budget`, coverage
and reconstruction declarations, including `Recon.pre`, `pre_noHit` and
`firstReturnExt`; the interval observer and seam requirements; and the finite
`growthCheck_correct`, `growthCheck_false_bound`, `push_target_forced` and
`forced_reverse_pop_loop_noFiniteModel` chain. The receipt preserves its full
declaration inventory and final readback. The reviewer made no source edits
or builds during the final pass.

Supporting pure-Python checks also passed:

```sh
python3 experiments/check_lean_rank_milestones.py
python3 experiments/check_rank_query_first_return.py
```

The first covered 8,191 words through length 12, 98,305 prefixes and 16,434
successive milestones. The second covered 258 literal first returns, 8,822
edges and 86,408 product-simple path checks at seed `2026091828`.
Both explicitly reported native Lean as NOT RUN. A separate ephemeral
terminal-rank enumeration covered 1–3 states and words through length 6;
its exact snippet and counts are preserved in the acceptance receipt from
the review comment. These bounded checks support falsification, not the
all-input theorem or a new comprehensive terminal stress claim.

The two prose suggestions are resolved. The reviewer found no remaining
substantive issue in the supplied terminal/finite arguments. This records
agent review of the supplied argument, not publication acceptance by a venue,
a blind proof discovery or an external human review. Later changes to those
arguments require a fresh affected-source readback.

Licensing, author metadata, stronger numerical claims, practical completion
on every input and new signatures remain outside this gate.

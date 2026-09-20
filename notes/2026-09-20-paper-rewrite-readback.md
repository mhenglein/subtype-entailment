# Standalone paper rewrite and readback

Date: 2026-09-20. Actor/session: `paper-rewrite-20260920`, parent writer and
owner-authorized documentation integrator. Issue [#56](https://github.com/mhenglein/subtail/issues/56),
coordination [#37](https://github.com/mhenglein/subtail/issues/37), A010/A018.
Base: `987bd2f348507d62a3393770487cce599a2edf96`.

## Target and route

Expose the exact C081 arbitrary-tree bottom/product decision as an ordinary,
standalone mathematical argument. Preserve complete constructions and both
directions, distinguish inherited methods from the joint terminal preimage,
and move administrative evidence outside the manuscript. This is exposition
and comparison work; no Lean source or scientific claim is changed.

The route remains normalization, canonical least model, minimum-stack
factorization, finite flagged summary and absorption, followed by the terminal
rank/whole-conjunction preimage decision and the periodic continuation decision.
The disputed presentation obligation is whether an outside reader can recover
the finite diagram checks and one-word reconstruction without opening Lean.
The existing ordinary regular-countermodel and constant-free guarded transfer
proofs are presented explicitly, separately from the seventeen checked results.

## Review protocol

- Parent writes the manuscript, bibliography, maps and artifact documentation.
- `extension_proof_plan` reads the manuscript before Lean or old review notes,
  then compares critical revised passages with source. This is a separate
  review context with inherited project history, not independent rediscovery.
- `henglein_rehof_review` refreshes the primary-source HR97/HR98/NP99/NP03
  account, bibliography and bounded forward/backward comparison. It owns no
  files and does not certify complete absence of prior equivalent work.
- Both reviewers have read-only scope. Parent integrates and checks findings.
- No fresh Lean build/kernel replay or performance benchmark is implied by
  this prose-only change. Mapped proof sources retain their existing pin.

## Current changes

The introduction explains the exact theorem and proof strategy, and credits
Henglein–Rehof for structural complexity, nonstructural hardness and constraint
automata. Conventional numeric citations and a bibliography replace source
URLs embedded in administrative prose. The explicit-top/valuation distinction
is retained; no PSPACE lower bound is transferred without a proof.

All internal A/C/P/Q IDs, issue links, source hashes, audit narration, stale
benchmark figures and licensing administration are removed from the manuscript.
Author placeholders remain by owner request. The artifact guide preserves
source pins and historical reviews. Conventional theorem numbers replace the
old P-numbers; the JSON map retains those IDs as historical aliases.

The ordinary proof now explicitly gives the predecessor truncations for each
Horn rule, balanced saturation soundness/completeness/termination, all flagged
instance components, and the finite diagram consistency conditions. It retains
the shared interval products, positive lengths, coincident origins, overlap,
empty pieces and endpoint self-loop cases. A missing backslash in a displayed
`qquad` was corrected. Regular countermodels and the guarded constant-free
PSPACE transfer have complete ordinary proofs and explicit implementation and
formalization limits.

## Mathematical review and corrections

The separate reviewer read Sections 3–11 and Propositions 12.1–12.2 at
`8bbe7fc673b18c7c39a6aa5b6fa347d45df37334`, then compared critical Lean source
at `987bd2f348507d62a3393770487cce599a2edf96`. It reported four findings:

| Finding | Correction | Source correspondence |
|---|---|---|
| First-emission state names could confuse old `q_0` with the first fresh group, also numbered zero | Section 7.5 now uses `q_old` and `q_fresh`, explicitly relates them to the generator's `q_0,q_1`, and states the exact reverse transition, Bad/diagonal and origin-mask checks | `RankQueryCompiler.validDiagram` and `baseAtoms` already check the first fresh state correctly |
| Root and endpoint Boolean tests were underdefined | Section 6.1 defines `root_j=[j=0]`, `end_j=[j=m]` and fresh root=false | `RankQuerySound.colB` |
| The auxiliary core-slot bound could be read as a bound for every compiled variable | Section 7.2 states the total carrier bound `2 + groups + r`, accounting for two fixed variables and one origin per group | `RankQueryCompiler.Var`, `compileValid`; `RankQueryCoverage.coreBound` |
| Observer tuple sorts were implicit | Section 7.1 specifies source/target controls, colours and the move relation | `RankQuery.Observer` |

The reviewer checked only these corrections at
`3cebfff409c1d76ffc238d678f48150738413433` and accepted all four, with no
correction-specific issue. Parent then made the carrier size explicitly
"at most" in `7d7280e`, matching the diagram's variable count bounded by `r`.
This final wording change was checked by the parent against `Var` and
`compileValid`; it was not a second full referee pass.

The reviewer found no additional confirmed mathematical failure in terminal
rank, graph surgery, finite diagram coverage, the common-word interval
product, finite promotion iteration, the periodic monitor or extraction.
The targeted correspondences included `RankQueryCoverage.coverage` and
`closure_iff`, the finishing/completion declarations, terminal decision,
bounded-cycle equivalence, periodic monitor acceptance and final entailment
correctness. This is a scoped ordinary-proof and source readback, not a fresh
proof of every supporting source lemma or a new build/axiom audit.
The reviewer inherited project history. Its separate reading context is not
independent rediscovery. No proof source was weakened or changed to resolve
an exposition finding. Its read-only scope is released.

## Literature review and limits

The separate primary-source reviewer refreshed these exact comparisons:

- **HR97**, Theorems 4.7–4.8 and Corollary 4.9: structural finite simple types;
  coNP completeness over a nontrivial lattice, hardness already with a
  covariant binary constructor. The stale PDF URL was replaced by the
  [LICS proceedings record](https://lics.siglog.org/archive/1997/HengleinRehof-Thecomplexityofsubt.html)
  and DOI `10.1109/LICS.1997.614961`.
- **HR98**, Section 3 and Theorems 1–2: constraint automata and nonstructural
  PSPACE hardness with explicit bottom/top, product and arrow in the ambient
  domain. Theorem 5 concerns structural infinite-tree entailment over a lattice
  of constants. Its stated theorem does not explicitly say "nontrivial";
  this word was retained only for HR97. [Proceedings record](https://link.springer.com/chapter/10.1007/BFb0055089).
- **NP99**, Theorem 14: product equations and variable inequalities over
  finite or possibly infinite bottom/product/top values, P-automata and PSPACE
  completeness. The bibliography now includes LNCS 1742 and
  [the DOI](https://link.springer.com/chapter/10.1007/3-540-46674-6_22).
- **NP03**, Theorems 1, 2, 4 and Lemma 1: the cap-automata/shared-word
  characterization, preserving finite/regular/arbitrary-tree distinctions.
  It is not imported as a general decision algorithm.
  [Author's publication record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:02.html).

The reviewer did not freshly verify SANPT06 or BPR19. Parent checked the
[official SANPT06 record](https://www.ps.uni-saarland.de/Publications/details/fot:04.html),
the [BPR19 slides](https://lipn.univ-paris13.fr/~breuvart/articles/NSSA_journee.pdf),
the [KMP77 publisher record](https://epubs.siam.org/doi/abs/10.1137/0206024),
and [Schubert's withdrawal metadata](https://arxiv.org/abs/2109.02458).
Those checks establish bibliographic identity and the limited roles stated
in the paper, not full theorem audits of SANPT06 or BPR19. The slide
announcement is not used as a preimage theorem. The withdrawn result is not
used as a decision theorem. No missing journal pagination was invented.

The reviewer suggested removing an unavailable unpublished memo citation.
Parent retained its explicit unpublished attribution because it is part of
the actual provenance; the manuscript supplies the needed ordinary proofs.
An unsupported reference to earlier Henglein–Rehof–Urzyczyn notes was removed.
Authorship is not inferred. The bounded comparison found no inspected theorem
subsuming the exact full result, but does not establish absence of such a
theorem or publication priority. Full-input lower-bound transfer, exact
terminal-compiler comparison and explicit-top decidability remain separate
questions. The literature reviewer's read-only scope is released.

## Final artifact and validation

The final PDF was rendered locally from committed source
`1a66d211c92acda331cf893c04da3e2255dd03af` with Pandoc 3.11 and Tectonic 0.17.0.
It has **25 A4 pages**. Parent visually inspected every page of that rendering
for readable equations, clipping, missing glyphs, headers, page numbers,
section transitions and citations. The final bibliography occupies one page;
proof-end markers remain with their preceding text.

PDF SHA-256:
`2f39d5c9c002cd61973c6e220e7b407658c5f2332fa42c16707c0c0e32425743`.
The [manifest](../output/pdf/subtail-paper-manifest.json) has
`source_files_match_render_revision=true` and retains the mathematical pin
`c946d86b9e65da2877e0df42c710abbdcb5a4037`.

| Check | Outcome and scope |
|---|---|
| `python3 paper/check.py` | PASS: seventeen checked-source result mappings, three separately labelled ordinary results, source byte identities, bibliography and literal examples; no Lean replay |
| `python3 paper/build.py` | PASS: final committed sources and manifest above |
| `pdftoppm -r 105 -png output/pdf/subtail-paper.pdf ...` plus page inspection | PASS: all 25 final pages |
| `python3 scripts/research_index.py --check` | PASS: eighteen approaches, 159 canonical records, local paths and ID links |
| `python3 -m unittest discover -s scripts -p test_research_index.py` | PASS: thirteen navigation tests |
| `python3 notes/prior-work/check_scholarship.py` | PASS: 26 source records, 121 local links and two independent fixtures; this script is not a proof review |
| `python3 -m unittest discover -s notes/prior-work -p test_search.py` | PASS: nine literature-search tests |
| `git diff --check` | PASS |
| New Lean build, kernel replay and solver benchmark | NOT RUN; no Lean, algorithm or experiment source changed |

Earlier render attempts exposed a `stmaryrd` size substitution. Removing the
package caused an undefined bracket command; declaring its shape before its
family also failed. The final header retains the package and declares a
scalable family/shape in the correct order. Those failed render attempts
produced no mathematical result. The final log has no missing character,
undefined citation, overfull/underfull box or font-size warning. One benign
Pandoc template notice remains: `Unused \captionsetup[table]`.

Main `987bd2f`'s previously pending Lean CI completed PASS during this work:
[run 35484749771](https://github.com/mhenglein/subtail/actions/runs/35484749771).
That evidence is separate from this documentation revision. The new changes
match the Research checks workflow, but do not trigger Lean, experiment or
replay workflows. An absent run is not a new pass. Final main SHA, actual CI
outcome, stable tag and integration lease release are recorded in
[#56](https://github.com/mhenglein/subtail/issues/56) and
[#37](https://github.com/mhenglein/subtail/issues/37).

The owned branch and prior checkpoints are retained. No unrelated workspace,
branch, stash or unpublished contribution is claimed to have been audited or
retired. The best next implementation target is a complete regular-countermodel
extractor with its precise correctness interface. Authorship, licensing,
human review and the unresolved mathematical extensions remain open.

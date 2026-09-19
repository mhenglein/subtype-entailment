# Core non-structural subtype entailment lineage: primary-source audit

**Date:** 2026-09-19
**Scope:** bounded primary-source readback of NP99, NP03, Priesnitz Chapter 11,
Schubert v1/v2, and the BPR19 deck, plus a targeted archival search. This is a
literature and transfer audit. It does not change any Subtail proof status.

The current target is Problem 1.7: for a finite normalized constraint set
`C`, decide whether every assignment satisfying `C` satisfies `alpha <= beta`.
Subtail assignments are arbitrary, possibly-infinite prefix-closed binary
product trees; bottom is the leaf case and the greatest element is the full
infinite binary tree. The current repository has a checked summary bridge and
terminal branch, while infinite continuation normalization and final
composition remain open.

## Source map

| ID | Source status | Safe repository use |
|---|---|---|
| PW-NP99 | verified restricted theorem | benchmark and semantic warning |
| PW-NP03 | verified journal/precursor lineage | cap-language prior art |
| PW-PRI04 | verified local lemma counterexample | boundary-split regression |
| PW-SCH21 | v1 readback; v2 withdrawn | failed global-extension precedent |
| PW-BPR19 | author slides only | announced restriction requiring verification |

The relevant follow-up cards are in [`notes/prior-work/agent-tasks.md`](../agent-tasks.md).

## PW-NP99 — restricted PSPACE benchmark

**Primary sources and locators.** Niehren and Priesnitz, “Entailment of
Non-Structural Subtype Constraints,” ASIAN 1999, pp. 251–265:
[record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:99.html),
[PDF](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf),
[DOI](https://doi.org/10.1007/3-540-46674-6_22). The relevant statements are
Section 2, Proposition 1, Table 1, Proposition 2, Proposition 13, and
Theorem 14 in Section 6.

**Source result.** The paper uses the ambient signature
`Sigma_2 = {bottom, top, product}`, with binary product and pointwise label
order `bottom < product < top`. It distinguishes finite trees from all trees,
where the latter include possibly-infinite trees. Its restricted grammar is
`phi ::= u = u1 x u2 | u1 <= u2 | phi and phi`; explicit `x = bottom` and
`x = top` constraints are excluded, as are unary constructors. Proposition 1
gives PSPACE hardness for the restricted language in both tree structures.
After closure and clash conditions (Table 1 and Proposition 2), Proposition 13
reduces closed, clash-free entailment to universality of a finite automaton over
`{1,2}*`; Theorem 14 states PSPACE-completeness for finite and all
possibly-infinite trees. The final discussion gives an explicit-top example
where that automaton is not universal although entailment holds, so an extra
periodic edge is needed.

**Transfer analysis.** This is a useful restricted benchmark, not a solution
of Problem 1.7. Syntactic absence of constants does not remove top or bottom
from valuations. A transfer would need a two-way valuation map between the
ambient NP99 model and Subtail’s top-free product-node model, preservation of
arbitrary-tree quantification, and an effective translation of constraints.
None is supplied by NP99. Do not cite Theorem 14 as a Subtail decision
procedure or as a finite witness bound.

## PW-NP03 — cap languages and shared word equations

**Version and locators.** Niehren and Priesnitz, “Non-Structural Subtype
Entailment in Automata Theory,” Information and Computation 186(2), 319–354
(2003): [record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:02.html),
[journal PDF](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf),
[DOI](https://doi.org/10.1016/S0890-5401(03)00140-8). The separate TACS 2001
precursor is [SubTypeEntailment_01.pdf](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_01.pdf).
The journal PDF is 46 pages; the precursor is 23 pages. The corresponding
main reductions are journal Theorems 1, 2, and 4, versus precursor Theorems 13
and 34. The journal explicitly includes regular trees alongside finite and
possibly-infinite trees.

**Source result.** Section 2.1 models trees as prefix-closed,
arity-consistent partial functions and separates finite, regular, and infinite
domains. Section 2.3 uses bottom, top, and one covariant constructor `f` of
arity `n`. Section 3 defines
`E ::= R1 R2^cap | E1 union E2`, where the cap operation takes prefixes of
powers of one word from a regular language. Lemma 1 exposes the shared-word
equation `pi nu = mu pi`; Corollary 2 places the problem in a positive
`forall exists*` word-equation fragment with regular constraints, while
Corollary 3 settles only the unary-constructor case. Theorem 1 characterizes
one-constructor NSSE by universality of restricted cap expressions. Theorem 2
gives a polynomial reduction to cap-automaton
universality; Theorem 4 gives the reverse translation for complete restricted
cap automata.

**Transfer analysis.** NP03 is the closest inspected source for Subtail’s
shared continuation word, regular state guards, and repeated endpoint
comparisons. It supplies audit questions: identify the single word and its
quantifier scope; separate regular guards from the cap component; and verify
the restricted/shuffle hypotheses. Transfer remains open because Subtail has no
top leaf, uses ordered endpoint flags, and has not been mapped to NP03’s
left/right safety automata. No finite bound for all current continuation words
follows. Treat the theorem as an equivalence of decision problems, not an
executable solver.

## PW-PRI04 — Chapter 11 boundary-split failure

**Primary source and locator.** Tim Priesnitz, *Subtype Satisfiability and
Entailment*, Saarland doctoral thesis (title-page year 2004; colloquium 1 April
2005), [PDF](https://d-nb.info/986396834/34). Relevant material is printed
pp. 111–114, PDF pages 125–128: the definition of “straight,” Theorem 11.1,
and Lemmas 11.1 and 11.2.

**Independent readback.** The printed definition calls a regular language
`R` straight when it contains no complete set `pi mu*` with `mu` nonempty.
Theorem 11.1 claims decidability of cap-expression universality over straight
regular expressions. Lemma 11.1 asserts that, for straight `R1` and regular
`R2`, `pi1 pi2 = mu1 mu2` forces both factor pairs to agree. The literal claim
is false: take `R1={0,01}`, `R2={1,11}`, and `w=011`. Then
`w=0·11=01·1`. Both languages are finite and therefore straight under the
printed definition, since `pi mu^k` has unbounded length when `mu` is nonempty.
The trie proof also fails: an accepting `0` state can continue on `1` to
accept `01`, so merging accepting states with the second automaton’s start can
create a boundary-label conflict. Prefix-freeness of the left language repairs
this lemma alone; it does not repair Lemma 11.2 or Theorem 11.1.

**Transfer analysis.** This is a regression for terminal capture and
first-return arguments. Finiteness, acyclicity, straightness, or regularity do
not establish unique boundary splits. A Subtail proof needs prefix-freeness,
an explicit separator, or another proved uniqueness invariant, including empty,
overlapping, and recurrent cases. This local failure does not refute the
thesis theorem as a whole, NP03, BPR19, or any Subtail claim.

## PW-SCH21 — withdrawn global extension

**Primary source and locator.** Schubert, [arXiv:2109.02458](https://arxiv.org/abs/2109.02458),
[v1 PDF](https://arxiv.org/pdf/2109.02458v1), submitted 6 September 2021.
The record says v2 was revised 20 December 2021 and withdrawn because of a
formulation error in Lemma 5.5 that invalidates the later construction; its v2
PDF is unavailable. I read v1 pp. 15–16: Definitions 10 and 11, Proposition
5.4, and Lemma 5.5.

**Exact inspected premise and status.** For some `i in {0,1}`, Lemma 5.5
assumes that the static decoration of `alpha` at `g` is contained in
`{bottom_i}` and that `S(alpha)|g = bottom_i`. It concludes that the extended
substitution `S_hat^g_{alpha,i}` satisfies every inequation in the original
finite set `E`; if `S` avoids constants, the extension also avoids them.
Definition 11 changes dynamically decorated accessible positions to a
homogeneous product of the selected constant and changes the designated
position. Proposition 5.4 supplies the intermediate global properties. The
withdrawal makes the construction unsupported, but the concrete failing `E`,
`S`, `alpha`, `g`, `i`, and falsified inequation remain **UNKNOWN** here.

**Transfer analysis.** The useful warning is proof shape: changing one
solution must preserve all constraints simultaneously. This resembles Subtail
whole-conjunction and shared-interval obligations, but the signatures and
domains differ. Earlier Schubert definitions may remain usable; no failure
fixture or counterexample to C080 has been established.

## PW-BPR19 — slide-level restriction only

**Primary source.** Breuvart, Penelle, and Rehof, *New results on the
Non-Structural Subtype Entailment Problem*, author-hosted [slide PDF](https://lipn.univ-paris13.fr/~breuvart/articles/NSSA_journee.pdf),
dated 7 November 2019. The displayed deck is numbered 1/16–16/16; the PDF
contains one extra container page. I read slides 6–16.

**Inspected announcements and caveats.** The deck starts from inductive or
coinductive types with bottom, top, product, and arrow, then restricts to
product and simple equations with conclusion `x <= y`. It announces a
2-EXPTIME restriction excluding homogeneous products `bottom x bottom` and
`top x top`, and an alternative quotient system identifying those products
with bottom and top. Its cap-language reduction uses regular components,
suffix-close/saturated `K`, and finite `F` or `F_i` selections for ultimately
periodic continuations. The deck labels the claimed Büchi-automaton PSPACE
step a “white lie”; a later slide asks how to return from the infinite
completion and lists prefix closure and saturation as conditions. The final
slide says the deterministic-cap restriction from Priesnitz is false as stated
in the thesis. These are slide-level claims and presentation caveats, not a
reconstructed proof failure.

**Transfer analysis.** BPR19 is valuable prior art for finite periodic
selection and saturation, but it is not an imported theorem. No full proof,
formal size bounds, or translation to Subtail’s top-free arbitrary-tree model
with ordered endpoint flags was located. This audit therefore cannot verify
whether the listed return-to-finite-language conditions are discharged in the
claimed restriction. Keep the result announced pending archival verification.

## Bounded archival search

Searches run on 2026-09-19:

| Query or path | Disposition |
|---|---|
| Exact BPR19 title, with “paper,” “full paper,” and author names | Deck only; no formal paper located. |
| `site:hal.science` and `site:arxiv.org` title searches | No BPR19 record; arXiv result was Schubert. |
| Crossref title API query | No BPR19 DOI/title among returned records; NP99/NP03 records appeared. |
| LIPN author page and `articles/` path | No paper index exposed; named deck remained available. |
| Schubert arXiv history and v2 PDF path | Withdrawal note confirmed; v2 PDF returned unavailable. |
| Public fetch of GitHub issues #36/#37 | Returned 404 in this environment; not treated as source evidence. |

No author contact was made. Search absence is **UNKNOWN**, not a negative
publication result. The primary PDFs were kept under `/tmp/subtail-literature-20260919/`
and checked with `pdfinfo`, `pdftotext -layout`, and `pdftoppm`; thesis pages
were visually inspected. The Priesnitz witness was independently enumerated.
No paper or extracted page was added to the repository.

## Agent-facing synthesis and limits

Across the sources, four obligations recur: preserve the ambient semantics
(especially top versus full infinite tree); preserve one shared continuation
word or substitution across the entire conjunction; prove boundary-factor
uniqueness rather than infer it from straightness or acyclicity; and give an
effective finite completion with its size and soundness proof. These are audit
criteria, not discharged Subtail lemmas.

For any future transfer, record the exact source version and locator, the
constructor signature and tree domain, the input and conclusion quantifiers,
the translation in both directions, its termination or size bound, and the
semantic conclusion actually obtained. Mark each direction independently.
“Related cap language,” “same-looking periodic word,” or “accepted by a
finite automaton” is useful navigation but is not a theorem transfer. A
bounded search, an inaccessible version, or a slide announcement must remain
clearly separated from inspected mathematical text. The strongest reusable
artifact here is therefore a set of falsification and transfer checks, not a
new upper-bound claim.

New dependable readback in this pass is the NP99 grammar/Theorem 14 interface,
the NP03 `_02` versus `_01` version/theorem map, the independently checked
Chapter 11 witness, the exact Schubert premise with UNKNOWN failure fixture,
and the BPR19 finite-`F_i`/“white lie”/return-condition caveats. Follow-up work
is listed in `agent-tasks.md`; the relevant cards cover O01–O04 and the periodic-suffix interface O11. This audit did not
recheck every proof line of NP99 or NP03, inspect HR97/HR98, reconstruct
Schubert’s withdrawn counterexample, find a full BPR19 proof, or establish a
novelty claim. No claim status should be promoted from this file alone.

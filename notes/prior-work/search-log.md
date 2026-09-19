# Discovery provenance and coverage log

## What this record can establish

The September 18 initial pass organized known sources. It was then correctly reopened in [issue #36](https://github.com/mhenglein/subtail/issues/36) because organization had been overstated as broad discovery. The subsequent discovery comment [5737842853](https://github.com/mhenglein/subtail/issues/36#issuecomment-5737842853) contains the thesis example, Schubert locators and specialist-paper findings. Those are preserved here rather than left only in an issue conversation.

The consolidation baseline is `df222241dc1a55ac6ee5da3cba3aedf662b3e285`. Its five-file prior-work directory lacked the new dossiers. The present pass refreshed primary sources selectively and corrected bibliographic metadata. It did not rerun an exhaustive citation database export or inspect every page of every paper. No unverifiable count of papers read or sites searched is claimed.

## Recovered discovery queries and families

Earlier visible discovery used queries including `"non-structural subtype" thesis`, `"subtype entailment" Breuvart Penelle`, `"cap automata" decidability`, `"subtype entailment" "RAIRO"`, `"pattern languages" "regular constraints" universality`, and `"conjunctive regular path queries" "inverse" "transduction"`. It also searched author archives and specialist venue names. This is a recovered set from the conversation, **not a complete timestamped search export**. Irrelevant or empty results do not certify absence of prior art.

In the consolidation pass, exact-title searches for `"Negated String Containment Is Decidable" MFCS 2025` and `"On the Complexity of the Matching Problem of Regular Expressions with Backreferences" 2026` recovered working Dagstuhl entity pages after direct DOI-path fetches failed. These are existing Subtail sources, not newly discovered papers.

## Primary-source inspection recorded in this pass

| Source/family | Actual inspection | Result / limit |
|---|---|---|
| Priesnitz thesis, national-library PDF | Title pages; Chapter 11 definition/lemma; page images at printed pp. 111 and 113; surrounding parsed text | Literal Lemma 11.1 counterexample preserved. Not a whole-thesis review. |
| Schubert arXiv record and v1 | Withdrawal/version record; Definition 11, Proposition 5.4, Lemma 5.5 passages | Identified global substitution-extension claim. Concrete failure reconstruction still open. |
| Reidenbach–Schmid, Kybernetika | Publisher record; Definition 3.7; Theorems 3.9/3.15 and surrounding definitions | Positive/negative reversal-bound distinction, no transfer to Subtail. |
| Karhumäki–Saarela, DMTCS | Publisher record; Theorem 5.2 and its cited older result | Noneffective regularity warning; older biprefix source not independently inspected. |
| Karhumäki–Saarela, Fundamenta Informaticae | Author archive/PDF; Theorem 2.1 and construction context | Language-monoid distinction. Not ordinary finite-word factorization. |
| Breuvart–Penelle–Rehof | Author-hosted slide deck refreshed | Announced restriction retained; no archival full proof located. |
| Barceló–Figueira–Romero | arXiv record/abstract | Corrected authors and duplicate entry; no graph-preimage theorem audited. |
| Thompson–Freydenberger | Publisher metadata and full-text theorem sections | Corrected actual authors; richer-language boundary, not a terminal-copy reduction. |
| MFCS 2025 negated containment | Dagstuhl record and report abstract refreshed; theorem locator retained from older Subtail proof note | Existing source restored. Theorem 28 not represented as a fresh complete proof audit. |
| ICALP 2026 backreference matching | Dagstuhl record/full HTML, canonical-form Theorem 6 | Existing source restored; fixed-expression matching versus containment distinguished. |
| Henglein–Rehof / Su et al. | Primary bibliographic metadata plus existing source-linked repository audit | Corrected title/year/version conflations. Not a fresh replay of every historical reduction. |
| IJFCS 2025 corrigendum | Historical metadata lead; attempted publisher retrieval unsuccessful | Full repair uninspected. Keep O08 open. |

## Specialist-venue coverage: explicitly partial

Kybernetika, DMTCS and Fundamenta Informaticae yielded named, inspected papers. RAIRO and IJFCS yielded citation/metadata leads that are not complete proof audits. Theory of Computing Systems supplied an inspected adjacent query paper. Author pages, a national-library thesis copy, arXiv and Dagstuhl proceedings complemented the title searches.

This was **not** a venue-by-venue exhaustive sweep of every volume, a complete forward-citation crawl of Niehren–Priesnitz, or a search of all languages and dissertations. No paid bibliographic-database coverage is claimed. The [open obligations](open-obligations.md) retain those gaps.

## Freshness and provenance rules

The 1997/1998, 1999/2003 and POPL/manuscript/journal versions must be deduplicated by lineage, not counted as unrelated discoveries. The 2014 TLCA status page and 2016 thesis are historical observations, not 2026 status certificates. Current arXiv withdrawal status outranks an old abstract snippet. An author-hosted slide theorem is marked as announced until a full proof is located.

Primary-source URLs and locators are recorded; no downloaded paper bytes, extracted PDF pages or access tokens are committed. Where inspection is historical, the register says so. The result of this search is a stronger map of evidence and failure mechanisms, not a proof that there is no undiscovered solution or equivalent theorem.


## Structured review continuation, 2026-09-19

Repository baseline: `064fc7306b679bf607b91e7d8de259823f200c62`.
Exact queries, source URLs, inspected locators and candidate dispositions are
recorded with the work that used them:

- [Core lineage and failed proofs](dossiers/core-lineage-review-2026-09-19.md).
- [Word equations, borders, containment and graph queries](dossiers/adjacent-methods-review-2026-09-19.md).
- [Periodic continuations and finite representations](dossiers/periodic-continuations-review-2026-09-19.md).

These were complementary source passes, not blind independent reviews of the
same theorem. The parent inspected critical source statements and reviewed
worker drafts. Errors or overbroad formulations found in draft review were
corrected before handoff; that does not certify every proof in every paper.

New register entries in this pass include the HHI periodicity source, the ABF
FDFA foundation, and a recent parameterized-periodicity lead that was screened
out. PW-BLLS25 and the word/query papers were already in the repository:
fresh theorem inspection is deeper evidence, not a newly discovered paper.
The 2014 status page and its recent search-visible repackaging are historical
context. Search snippets repeating Schubert's old abstract are not current
proof evidence.

Coverage remains bounded: no exhaustive forward-citation database export,
no paid-index search, no author contact and no claimed search of every venue
or dissertation. No named search round establishes the absence of an existing
solution. The two-round stopping criterion above is a proposed workflow;
it is not asserted to have been reached for all topic families in this pass.

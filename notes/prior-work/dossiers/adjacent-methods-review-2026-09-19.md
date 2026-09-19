# Adjacent methods review for Subtail

**Date:** 2026-09-19
**Checked revision:** `064fc7306b679bf607b91e7d8de259823f200c62`
**Scope:** issues #36 and #37, focused on C067, C077 and the C080 graph-query
proposal. This is a source audit, not a new theorem or novelty claim. C029
periodic-tail work and the fresh BLLS25 saturation inspection are excluded;
the parent task covers them.

## Result at a glance

| Source | Exact result | Safe reuse | Direct-import limit |
|---|---|---|---|
| DGH01, Thm. 4 | Existential word equations plus regular constraints over a free monoid with involution are PSPACE-complete. | Backend for one explicitly constructed C067 formula. | No scheme completeness or universal-cut elimination. |
| BORD09, Thm. 58, Cor. 62 | An $n$-state NFA with an unbordered word has one of length at most $6n+1$. | Pumping pattern for a coloured proof with a stated closure invariant. | Ordinary borders carry no state colours or flags. |
| HHL25, Thms. 28–29 | One negated factor-containment atom with regular/chain-free constraints is decidable. | Exact one-anchor check such as $Za\not\preceq XZ$. | Repeating the solver does not decide a synchronized multi-atom conjunction. |
| KU26, Thms. 6–8 | Fixed one-use backreference matching has an ABCBD canonical union and an input-word matcher. | Audit of one terminal copy on one supplied word. | No regular-language containment or unbounded witness search. |
| BFR19, Props. 3, 12, Thm. 11 | UC2RPQ boundedness is a finite-expansion-cover problem reducible to distance-automaton limitedness. | Design pattern for C080 after its graph inverse image is proved. | Standard path atoms choose words independently; they do not share a generator variable. |

The operational rule is to classify a proposed import first: fixed-word
membership, one factor-avoidance atom, synchronized conjunction, or bounded
expansion cover. Keep the source's quantifier order unchanged.

## DGH01: exact word equations with rational constraints

**Primary/version/locator.** Volker Diekert, Claudio Gutiérrez and Christian
Hagenah, “[The Existential Theory of Equations with Rational Constraints in
Free Groups is PSPACE-Complete](https://arxiv.org/abs/cs/0103018),”
`cs/0103018v1`, 26 March 2001; primary PDF, Section 4, Theorem 4, PDF pp. 7–8
(printed p. 8).

**Theorem and effective measure.** Input is a closed existentially quantified
propositional formula whose atoms are word equations and regular-membership
constraints over a free monoid with involution. The question is whether some
finite-word assignment satisfies it. DGH proves PSPACE-completeness. The input
formula and finite automata are finite; the theorem statement does not supply the explicit Subtail witness bound.

**C067 map.** Use the doubled involutive alphabet

`{0, 1, bar0, bar1}`

with the letter involution $0\leftrightarrow\bar 0$,
$1\leftrightarrow\bar 1$; on words the source involution also reverses order.
Constrain every C067 variable to the regular language `{0,1}*`. C067's terms
use only `0`, `1`, concatenation and variables, so no barred letter or
involuted variable is introduced. The shared
$W$, local factors $V,R,S,Z$, and prefix/suffix variables become existential
word variables; $A_t,L_t$ and $D_{(p,\neg t)}$ become NFA constraints. The
finite mismatch disjunction is expanded over the two ordered unequal letter
pairs. This is a polynomial-size formula once the C067 automata are given.

**Reusable idea / limit / next check.** Use DGH only after terminality and the
finite formula-to-witness equivalence are proved. It supports C067's
single-source terminal backend, not coverage of all schemes or cuts. The
smallest useful review is one expanded formula with all binders, alphabet
constraints and both implication directions. The existing nonterminal-final
example in the C067 notes must remain a prerequisite; an equation solver does
not repair that semantic failure.

## BORD09: ordinary unbordered regular-language witnesses

**Primary/version/locator.** Terry Anderson, John Loftus, Narad Rampersad,
Nicolae Santean and Jeffrey Shallit, “[Detecting palindromes, patterns and
borders in regular languages](https://cs.smu.ca/~nic.santean/art/detect.pdf),”
Information and Computation 207 (2009), Theorem 58, printed pp. 1114–1115
(PDF P18–P19), and Corollary 62, printed p. 1115 (PDF P20).

**Theorem and effective measure.** For an $n$-state NFA $M$, if all accepted
words in $[N,2N+6n+1]$ are bordered, then all longer accepted words are
bordered. Hence an accepted unbordered word exists iff one exists of length at
most $6n+1$. The proof uses the block-pumping Lemmas 55–56.

**Subtail transfer.** A coloured analogue must preserve the source state,
target state and flag of the selected comparison through every shortening.
The project's forward-closed target-colour adaptation records exactly this
extra hypothesis in [`source-border-anderson.md`](../../2026-09-05-source-border-anderson.md).
Without it, ordinary word equality is insufficient. Do not replace the
Subtail `Basic.Witness`/canonical checker with the ordinary predicate “equal
prefix and suffix”; that predicate omits the required endpoint and flag data.

**Falsification/next task.** Construct a direct run-state check for the
proposed pumping step and compare it with the canonical checker on the shortest
candidate where a removed block changes a suffix-start colour. A bounded
failure is `UNKNOWN`; a transfer needs a closure proof. C077's native
last-target construction remains the relevant recorded route; its canonical
claim contains the exact evidence status.

## HHL25: one negated containment atom

**Primary/version/locator.** Vojtěch Havlena, Michal Hečko, Lukáš Holík and
Ondřej Lengál, “[Negated String Containment Is
Decidable](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2025.56),”
MFCS 2025, article 56, pp. 56:1–56:20; publisher PDF, definition on 56:4,
Theorem 22 on 56:13, Theorems 28–29 on 56:16–17 (PDF P3, P12 and P15–P16).

**Theorem and effective measure.** A finite assignment to string variables must
satisfy regular/chain-free constraints and one atom
`not Contains(N,H)`, meaning there are no $u,v$ with $H=uNv$. Theorem 28 gives
decidability in ExpSpace; Theorem 29 allows a chain-free word-equation
conjunction plus that single atom. Theorem 22 gives the flat
regular-language replacement used by the algorithm.

**Subtail map.** A complete target anchor with final suffix $Y=Za$, prefix
`X`, and regular tail `Z` maps exactly to `not Contains(Za, XZ)`. The same `Z`
is shared in both terms, so this is a genuine one-anchor mapping and an
independent check of the native C077 construction.

**Limit/falsification.** HHL does not state arbitrary conjunctions of negated
containment atoms. The smallest useful audit is two anchors sharing one `Z`:
compare the direct shared-assignment predicate on a bounded word domain against
separate existential checks on that same domain. A discrepancy exposes the
independent-existential error; agreement is only bounded evidence. The next
task is to list which C077/C080 normal forms reduce to one atom; leave the
multi-atom case explicit rather than citing Theorem 28 repeatedly.

## KU26: fixed one-use backreference matching

**Primary/version/locator.** Soh Kumabe and Yuya Uezato, “[On the Complexity
of the Matching Problem of Regular Expressions with
Backreferences](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.135),”
ICALP 2026, article 135, pp. 135:1–135:25; publisher PDF, Definitions 1–2
and Theorems 6–9 on 135:3–135:6 (PDF P2–P5).

**Theorem and effective measure.** The matcher receives an expression $E$ and an input
word $w$. The stated word-length bounds hold for fixed $E$; the Uniformity
remark makes expression-dependent preprocessing explicit. Theorem 6 rewrites every 1-use REWB as $O(|E|^2)$
ABCBD branches plus a regular residual, with total construction size
$O(|E|^4)$; Theorems 7–8 give the corresponding matching bounds. An ABCBD
branch requires one decomposition $w=w_Aw_Bw_Cw_Bw_D$ with the two captured
blocks equal.

**Subtail map and limit.** A terminal copied interval can be audited as one
ABCBD branch, especially with $D=\epsilon$, but this decides one candidate
word. Subtail asks about regular path languages, runs, and multiple coloured
cuts. Matching samples or enumerates words; it does not prove containment or
finite coverage. The next check is to run Theorem 6 on the existing terminal
copy decomposition and verify that every newly created comparison is covered.
Do not use the result for $\omega$-use or unbounded internal recurrence.

## BFR19: UC2RPQ boundedness and graph expansions

**Primary/version/locator.** Pablo Barceló, Diego Figueira and Miguel Romero,
“[Boundedness of Conjunctive Regular Path
Queries](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2019.104),”
ICALP 2019, article 104, pp. 104:1–104:15; primary PDF, Proposition 3 on
104:5, Theorem 6 on 104:6, Proposition 12 on 104:10, Theorem 11 on 104:9–10
(PDF P4–P10).

**Theorem and effective measure.** A UC2RPQ chooses one regular path word per
path atom; expansions replace atoms by finite paths. Proposition 3 says
boundedness is equivalent to a uniform finite expansion cover and to finitely
many minimal expansions. Theorem 6 specifically says that, for an NFA language
`L`, finiteness of its proper-prefix, proper-suffix, or proper-factor-free
sub-language is PSPACE-complete. Proposition 12 builds in single-exponential
time a distance automaton $D_\Gamma$ that is limited exactly when the query
is bounded; Theorem 11 gives ExpSpace-completeness and finite-UCQ size bounds.

**C080 interface and limit.** A possible graph inverse image can represent
state/colour nodes and first-return paths, then use the distance automaton as a
bounded-rank backend. Standard C2RPQ atoms share endpoints, not a literal word
variable or physical interval. The encoding therefore needs an explicit
synchronizing product and a proof that expansions preserve the already-checked
C080 semantic closure. This review supplies no such reduction. The smallest
next test is a two-atom shared-generator instance: verify that the encoding
rejects independent path choices. Treat BFR as a design pattern, not a new
frontier result.

## Agent-use rules and handoff

* DGH: finite existential formula only; preserve the doubled alphabet map and
  all shared binders.
* BORD09: ordinary unbordered only; cite a coloured closure invariant before
  transferring any bound.
* HHL: one shared-assignment containment atom; do not split a conjunction.
* KU: input-word matching with expression-dependent cost; do not infer language containment.
* BFR: finite expansion-cover semantics; do not infer shared generators from
  shared endpoints.

These are import boundaries, not claims that the project lacks its own checked
C080 closure or C077 native construction. The dossier leaves those canonical
records authoritative.

## Search and evidence provenance

Exact searches included:

* `arXiv cs/0103018 Diekert Gutierrez Hagenah Theorem 4 free monoids with involution PDF`
* `Anderson Loftus Rampersad Santean Shallit Detecting palindromes patterns borders regular languages Theorem 58 PDF`
* `"Negated String Containment Is Decidable" Havlena Hecko Holik Lengal Theorem 28 PDF`
* `Soh Kumabe Yuya Uezato On the Complexity of the Matching Problem of Regular Expressions with Backreferences PDF`
* `Barcelo Figueira Romero Boundedness of Conjunctive Regular Path Queries Proposition 12 PDF`

Accepted primary evidence: the DGH arXiv PDF; Anderson's author-hosted PDF
and arXiv record; HHL's MFCS publisher PDF; KU's ICALP publisher PDF/HTML;
and BFR's ICALP publisher PDF. Search snippets, blogs, Wikipedia,
ResearchGate, and secondary surveys were rejected as theorem evidence. A
Stuttgart DGH journal-PDF URL was inaccessible; the arXiv primary version was
used. No source papers were added to the repository.

| Source key | Before this pass | This pass |
|---|---|---|
| PW-DGH01 | Existing record and C067 mapping note | Recovered Theorem 4 and checked the doubled-alphabet/domain obligation. |
| PW-BORD09 | Existing theorem and coloured-transfer notes | Recovered Theorem 58/Corollary 62 pages and the uncoloured boundary. |
| PW-HHL25 | Existing target-anchor record | Recovered Theorems 22, 28 and 29 and the one-atom boundary. |
| PW-KU26 | Existing terminal-copy audit | Recovered Definitions 1–2 and Theorems 6–9 with fixed-word quantifiers. |
| PW-BFR19 | Metadata-only record | Added the primary Proposition 3/12 and Theorem 11 inspection; no inverse-image theorem. |

The source papers were paraphrased; no long quotations are used. Remaining
claims belong in the existing C/Q records and `STATE.md`, not in this dossier.

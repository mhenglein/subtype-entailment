# Bibliography and inspection register

Stable source keys are mirrored in [sources.json](sources.json). Publication status and inspection depth are separate: a published theorem may have only metadata checked in this pass; a withdrawn paper may have its failed lemma inspected closely. `TEXT` means selected primary passages, not a complete proof audit. `RECORD` means primary bibliographic record/abstract. `HISTORICAL` means a named earlier repository audit supplies the theorem locator. `LEAD` is not an imported theorem.

## September 19 inspection update

The [core](dossiers/core-lineage-review-2026-09-19.md),
[adjacent](dossiers/adjacent-methods-review-2026-09-19.md), and
[periodic](dossiers/periodic-continuations-review-2026-09-19.md) dossiers record
fresh selected-text reads, exact import boundaries and retrieval failures.
The entries below preserve earlier inspection provenance; dated `review_record`
fields in sources.json point to later readbacks. TEXT never means whole-paper
proof certification. Fresh inspections of already registered sources are not
counted as new discoveries.

## Direct lineage

| Key | Source and primary link | Version / inspection |
|---|---|---|
| PW-HR97 | Fritz Henglein; Jakob Rehof. **The Complexity of Subtype Entailment for Simple Types.** LICS 1997, pp. 352–361. [Author record](https://hjemmesider.diku.dk/~henglein/bib/publications/here97b.html) | RECORD. Distinct from the next paper. |
| PW-HR98 | Fritz Henglein; Jakob Rehof. **Constraint Automata and the Complexity of Recursive Subtype Entailment.** ICALP 1998. [Author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf), [DOI](https://doi.org/10.1007/BFb0055089) | HISTORICAL: [original audit](../literature-check.md). Full ambient signature matters. |
| PW-NP99 | Joachim Niehren; Tim Priesnitz. **Entailment of Non-Structural Subtype Constraints.** ASIAN 1999. [Author record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment%3A99.html), [PDF](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf) | TEXT refreshed September 19: restricted grammar, Propositions 1/13 and Theorem 14; earlier selected-text audit preserved in sources.json. |
| PW-NP03 | Joachim Niehren; Tim Priesnitz. **Non-structural subtype entailment in automata theory.** Information and Computation 186(2), 319–354 (2003); TACS 2001 precursor. [Journal author manuscript](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf), [TACS precursor](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_01.pdf), [DOI](https://doi.org/10.1016/S0890-5401(03)00140-8) | TEXT refreshed: journal Theorems 1/2/4, Lemma 1 and Corollaries 1–3; precursor theorem numbers differ. |
| PW-PRI04 | Tim Priesnitz. **Subtype Satisfiability and Entailment.** Saarland doctoral thesis, title-page year 2004; colloquium 1 April 2005. [National-library PDF](https://d-nb.info/986396834/34) | TEXT and page images: Chapter 11, printed pp. 111–114. Local Lemma 11.1 finding; not a blanket rejection of the thesis. |
| PW-SU06 | Zhendong Su; Alexander Aiken; Joachim Niehren; Tim Priesnitz; Ralf Treinen. **The First-Order Theory of Subtyping Constraints.** TOPLAS 2006; extends POPL 2002. [Official record](https://www.ps.uni-saarland.de/Publications/details/fot%3A04.html), [extended manuscript](https://www.ps.uni-saarland.de/Publications/documents/fot_04.pdf) | RECORD refreshed; HISTORICAL theorem checks refer to manuscript numbering 3.10 and 5.10, not an asserted match to every publication. |
| PW-BPR19 | Flavien Breuvart; Vincent Penelle; Jakob Rehof. **New results on the Non-Structural Subtype Entailment Problem.** 2019. [Author slides](https://lipn.univ-paris13.fr/~breuvart/articles/NSSA_journee.pdf) | TEXT: 17-page slides. No archival full proof located; announced result, not silently treated as a journal theorem. |
| PW-SCH21 | Aleksy Schubert. **On non-structural subtype entailment.** [arXiv record](https://arxiv.org/abs/2109.02458), [v1 PDF](https://arxiv.org/pdf/2109.02458v1) | TEXT: Definition 11, Proposition 5.4, Lemma 5.5. v1 submitted 6 September 2021; v2 dated 20 December 2021 withdraws the paper. |

## Word languages, automata and query neighbors

| Key | Source and primary link | Locator / inspection |
|---|---|---|
| PW-BORD09 | Terry Anderson; John Loftus; Narad Rampersad; Nicolae Santean; Jeffrey Shallit. **Detecting palindromes, patterns and borders in regular languages.** Information and Computation 207 (2009). [Full-version record](https://arxiv.org/abs/0711.3183) | TEXT refreshed September 19: Theorem 58 and Corollary 62. Ordinary borders only; earlier terminal-copy audit preserved in sources.json. |
| PW-DGH01 | Volker Diekert; Claudio Gutiérrez; Christian Hagenah. **The Existential Theory of Equations with Rational Constraints in Free Groups is PSPACE-Complete.** [2001 preprint](https://arxiv.org/abs/cs/0103018) | TEXT refreshed September 19: Section 4, Theorem 4, pp. 7–8. Explicit monoid involution/alphabet mapping required. |
| PW-GAN13 | Vijay Ganesh; Mia Minnes; Armando Solar-Lezama; Martin Rinard. **(Un)Decidability Results for Word Equations with Length and Regular Expression Constraints.** [2013 preprint](https://arxiv.org/abs/1306.6054) | RECORD; quantifier boundary, not a theorem about every restricted cap language. |
| PW-KUF07 | Manfred Kufleitner. **A Proof of the Factorization Forest Theorem.** [2007 preprint](https://arxiv.org/abs/0710.5130) | RECORD; the finite-semigroup morphism is a hypothesis, not a produced border invariant. |
| PW-RS14 | Daniel Reidenbach; Markus L. Schmid. **Automata with modulo counters and nondeterministic counter bounds.** Kybernetika 50(1), 66–94 (2014). [Publisher](https://www.kybernetika.cz/content/2014/1/66), [PDF](https://www.kybernetika.cz/content/2014/1/66/paper.pdf), [DOI](https://doi.org/10.14736/kyb-2014-1-0066) | TEXT: Definition 3.7, Theorems 3.9 and 3.15. |
| PW-KS10 | Juhani Karhumäki; Aleksi Saarela. **Noneffective Regularity of Equality Languages and Bounded Delay Morphisms.** DMTCS 12(4) (2010). [Publisher](https://dmtcs.episciences.org/523), [PDF](https://dmtcs.episciences.org/523/pdf), [DOI](https://doi.org/10.46298/dmtcs.523) | TEXT: Theorem 5.2. |
| PW-KS11 | Juhani Karhumäki; Aleksi Saarela. **The Unique Decipherability in the Monoid of Regular Languages is Undecidable.** Fundamenta Informaticae 110(1–4), 197–200 (2011). [Author PDF](https://amsaar.gitlab.io/articles/kasa11ibarra.pdf), [DOI](https://doi.org/10.3233/FI-2011-537) | TEXT: Theorem 2.1; products of languages, not individual word parses. |
| PW-BFR19 | Pablo Barceló; Diego Figueira; Miguel Romero. **Boundedness of Conjunctive Regular Path Queries.** [2019 primary preprint](https://arxiv.org/abs/1904.00850) | TEXT refreshed September 19: ICALP Propositions 3/12 and Theorems 6/11. No Subtail graph inverse-image transfer supplied. |
| PW-TF24 | Sam M. Thompson; Dominik D. Freydenberger. **Languages Generated by Conjunctive Query Fragments of FC[REG].** Theory of Computing Systems 68, 1640–1682 (2024). [Publisher and full text](https://link.springer.com/article/10.1007/s00224-024-10198-4) | TEXT: Theorem 6 and language-fragment definitions; previous author placeholders removed. |
| PW-HHL25 | Vojtěch Havlena; Michal Hečko; Lukáš Holík; Ondřej Lengál. **Negated String Containment Is Decidable.** MFCS 2025, article 56. [Publisher](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2025.56), [technical report](https://arxiv.org/abs/2506.22061) | TEXT refreshed September 19: MFCS Theorems 28–29. One negated-containment atom; already registered before this pass. |
| PW-KU26 | Soh Kumabe; Yuya Uezato. **On the Complexity of the Matching Problem of Regular Expressions with Backreferences.** ICALP 2026, article 135. [Publisher](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2026.135), [full HTML](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.135/LIPIcs.ICALP.2026.135.html) | TEXT refreshed September 19: Theorems 6–8 and Uniformity remark. Input-word matching with expression-dependent cost. |
| PW-BLLS25 | Bohn; Li; Löding; Schewe. **Saturation Problems for Families of Automata.** ICALP 2025, article 146. [Publisher HTML](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.146/LIPIcs.ICALP.2025.146.html) | TEXT refreshed September 19: Section 2, Theorem 1 and Theorems 8–9. Saturation transfer remains unproved. |
| PW-REGEX25 | Szymon Łopaciuk. **Corrigendum: Inside the class of REGEX languages [6].** International Journal of Foundations of Computer Science (2025). [DOI](https://doi.org/10.1142/S0129054125920017) | LEAD / metadata-only from the discovery record. Publisher full text was not retrieved. Do not assert the exact repair or its downstream consequences. |

## Periodic-continuation additions

| Key | Source and primary link | Locator / inspection |
|---|---|---|
| PW-HHI00 | Vesa Halava; Tero Harju; Lucian Ilie. **Periods and binary words.** 2000. [Author manuscript](https://www.csd.uwo.ca/~ilie/JCTA00.pdf) | TEXT: manuscript p. 2, Lemmas 1–2; p. 4, Theorem 1. Period arithmetic is a possible C029 helper; no coloured transfer is claimed. |
| PW-ABF18 | Dana Angluin; Udi Boker; Dana Fisman. **Families of DFAs as Acceptors of omega-Regular Languages.** LMCS 14(1:15), 2018. [Author PDF](https://faculty.runi.ac.il/udiboker/files/fdfa.pdf) | TEXT: introduction pp. 1–3; later theorem retrieval timed out. Saturation matters. Theorem 5.7 locator comes from PW-BLLS25 and is not a fresh theorem-body audit. |
| PW-HNI26 | Rikuya Hamai; Yuto Nakashima; Shunsuke Inenaga. **The Parameterized Periodicity Lemma.** [arXiv:2608.21912v1](https://arxiv.org/abs/2608.21912v1), 22 August 2026. | RECORD: abstract and metadata; accepted SPIRE 2026 according to arXiv. Screened out of the current dependency path because equality permits renaming. |

## Historical context, not present-day status certificates

| Key | Source | Limit |
|---|---|---|
| PW-TLCA14 | [TLCA open-problem entry](https://tlca.di.unito.it/opltlca/opltlcasu23.html), Rehof's historical question | Earlier audit identifies a 2014 status snapshot. Not evidence that nothing changed by 2026. |
| PW-DOL16 | Stephen Dolan. **Algebraic Subtyping.** Doctoral thesis (2016). [Thesis copy](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf) | Earlier audit records a discussion of non-structural entailment. Algebraic/extensible semantics must not be substituted for the memo's model. |

## Correction history

The previous bibliography attached the 1997 *Simple Types* title to the 1998 ICALP DOI. Those are now separate entries. The speculative To/Libkin entry for arXiv:1904.00850 was erroneous and duplicated PW-BFR19; it is removed, not retained as an additional source. PW-SU06 distinguishes the 2004 manuscript filename from the 2006 journal publication. PW-TF24 uses the publisher's actual author name, **Sam M. Thompson**. No bibliography correction changes a mathematical claim's status.

September 19 version correction: the earlier NP03 row linked the TACS `_01`
precursor while citing journal manuscript numbering. The `_02` author manuscript
and `_01` precursor are now distinguished. Fresh theorem locators and inspection
levels are in the dated dossiers and source register.

# Periodic continuations: useful imports and representation traps

Review date: 2026-09-19. Reader: parent session `structured-literature-review-20260919`.
Repository baseline: `064fc7306b679bf607b91e7d8de259823f200c62`.
This is a literature-to-obligation map, not a new proof of C029.

## Why this topic now

At the baseline, [STATE](../../../STATE.md) records an exact normalized subtype
summary construction and the terminal/infinite split. The terminal alternative
has a checked Boolean decision. `InfWitness` still includes an original finite
witness followed by a safe finite stem and a nonempty safe cycle. Finding a
cycle alone does not decide that predicate.

The existing [C029 argument](../../2026-09-04-denials-and-continuations.md),
Section 4, treats arbitrary-length entry prefixes. Once a prefix enters the
absorbing region, its surviving forbidden comparisons predict finitely many
periodic futures. Its proposed monitor tests a fixed primitive period with
residue-indexed state sets and a conflict bit. That historical written proof,
not a new generic omega-automata construction, is the first object to audit.
Infinite continuation of an address is distinct from infinite type-tree semantics.

## PW-HHI00: a precise periodic-word lemma

**Source:** Vesa Halava, Tero Harju and Lucian Ilie, *Periods and binary words*
(2000). [Author manuscript](https://www.csd.uwo.ca/~ilie/JCTA00.pdf), printed
p. 2, Lemmas 1–2; p. 4, Theorem 1. The author's
[publication page](https://users.utu.fi/harju/combwords.htm) identifies the
journal version as JCTA 89 (2000), 298–303. Locators here refer to the manuscript.

**Inspected result:** for a finite word with positive periods p and q,
length at least `p+q-gcd(p,q)` forces period `gcd(p,q)` (Lemma 1).
Lemma 2 derives divisibility for a period q no larger than word length minus
the minimum period. The statement and short argument were read from the
author PDF. Theorem 1 preserves the set of periods in a binary replacement;
it is not a state-labelled automaton theorem.

**Proposed use, not a completed transfer:** isolate the periodic arithmetic in
C029 from its automaton bookkeeping. For equality of suffixes of `v p^omega`,
prove the phase and minimum-period assertions explicitly. Apply the lemma to
long enough finite factors, then justify the infinite conclusion. Preserve
the arbitrary entry prefix and the location of its last phase mismatch.

**Do not infer:** that the replacement word follows the same automaton run,
preserves flags, or gives a complete decision. Period-set preservation alone
does not supply any of those interfaces. This source is a helper candidate,
not a proposed replacement for the whole C029 argument.

## PW-BLLS25: saturation has an effective test after representation exists

**Source:** León Bohn, Yong Li, Christof Löding and Sven Schewe,
*Saturation Problems for Families of Automata*, ICALP 2025, article 146.
[Primary full HTML](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.146/LIPIcs.ICALP.2025.146.html).
Freshly inspected: Section 2 definitions, Section 3.1 Theorem 1 and its
loopshift/power-stability discussion, Theorems 8–9. This updates an existing
Subtail source, not a new literature discovery.

An FDFA has a finite leading transition system and a progress DFA for each
leading state. Saturation requires equal ultimately periodic words to have
consistent acceptance across their normalized prefix/period representations.
Theorem 1 decides saturation and full saturation in polynomial time and gives
polynomial-length conflicting representations on failure. Almost saturation
and the stated regularity problems have PSPACE-completeness results.

**Transfer gap:** Subtail would first need an effective FDFA recognizing the
intended continuation condition, including all earlier ordered flags. Neither
the representation nor its preservation under moving cuts is supplied by the
saturation test. A finite state set for the original graph is insufficient.
The inspected sections do not contain a BorderAvoid reduction.

**Decision:** keep as an alternative representation audit. First test whether
equivalent lasso presentations preserve the proposed acceptance condition;
retain cut phase and state identity. This is not the shortest current route
to checking the existing periodic-suffix monitor.

## PW-ABF18: the prerequisite, not a shortcut

**Source:** Dana Angluin, Udi Boker and Dana Fisman,
*Families of DFAs as Acceptors of omega-Regular Languages*, LMCS 14(1:15),
2018. [Author PDF](https://faculty.runi.ac.il/udiboker/files/fdfa.pdf).
Freshly read: pp. 1–3, including the model overview and saturation requirement.
Follow-up retrieval of later sections timed out. Theorem 5.7 is a locator cited
by PW-BLLS25; its body was not freshly inspected here.

The introduction distinguishes saturated families from arbitrary families and
summarizes effective operations and translations for the saturated setting.
Its ultimately periodic-word characterization assumes omega-regular languages.

**Use:** foundational reading if an FDFA proposal is actually pursued.
**Gate:** state whether acceptance uses normalized pairs, how the input family
is built, and which semantic property proves saturation. Read the exact
theorem before making it a dependency. The C029 finite monitor does not need
to be recast as a general FDFA merely because this framework exists.

## PW-HNI26: screened recent lead, different equality

**Source:** Rikuya Hamai, Yuto Nakashima and Shunsuke Inenaga,
*The Parameterized Periodicity Lemma*,
[arXiv:2608.21912v1](https://arxiv.org/abs/2608.21912v1), 22 August 2026;
record says accepted for SPIRE 2026. Only abstract and metadata inspected.

The result concerns parameterized periods, allowing symbol renaming, and
announces a sharp Fine–Wilf-type bound. Current Subtail comparisons use
literal binary-word equality with separate automaton state labels.
**Disposition:** outside the current dependency path. Revisit only if a
specific reduction explains why parameterized equality is appropriate.
Recency alone is not evidence of applicability.

## Exact next investigation: O11

**Input:** current C029 written argument, the exact `InfWitness` definition,
and the baseline summary/absorption interfaces. Check current main before work.
**Question:** is the fixed-period monitor equivalent to the absence of that
forbidden periodic future for every finite safe entry prefix?

1. Define phase at each word position and at the entry endpoint.
2. Separate positions before and after the last mismatch. Include the empty
   entry prefix, residue zero, diagonal flags and period one.
3. Prove the suffix-equality criterion, then the monitor invariant. A bound on
   two periods does not prove the bucket update or reset semantics.
4. Check that all infinite continuation cases are covered and that a returned
   finite prefix is an original witness with a remaining infinite safe path.

**Acceptable outputs:** an exact readback with every implication justified;
a counterexample preserving all stated assumptions; or a named remaining gap.
**Stop condition:** a phase/reset counterexample blocks the claimed monitor
equivalence. Preserve it before attempting a repair. This does not alone refute
decidability or the independently checked terminal result.
**Opposing-route question:** if a finite representation fails, is the failure
about this chosen invariant, or does a richer encoding meet a known hardness
boundary? No undecidability claim follows merely from failure of this monitor.

## Search record and limitations

The parent ran these web queries on 2026-09-19:

- `"Fine" "Wilf" periodicity theorem words p q gcd primary paper`
- `"Saturation Problems for Families of Automata" 2025`
- `"subtype entailment" decidability 2025 2026`
- `"subtype entailment" decidability after:2021`
- `"Uniqueness theorems for periodic functions" Fine Wilf 1965 pdf`
- `"Periods and binary words" Halava Harju Ilie 2001`
- `"Saturation Problems for Families of Automata" "Theorem 5"`
- `"Families of DFAs as Acceptors" 2018 saturation`

The 2001 query was corrected to 2000 using author bibliographic evidence.
The original AMS Fine–Wilf PDF failed retrieval; no inspection of its proof is
claimed. PW-HHI00 supplies a freshly inspected word formulation instead.
Following the 2025 paper's reference to PW-ABF18 is one backward citation step,
not a complete citation crawl. The recent parameterized result is a screened
lead, not a newly applicable algorithm. A surfaced OpenTCS page explicitly
reuses the 2014 TLCA snapshot and was excluded as current-status evidence.
Search results also repeated Schubert's withdrawn abstract, reinforcing the
need to inspect version status. No absence-of-solution or priority claim is made.

# Subtail — current research state

Navigation updated: 2026-09-08. Scientific evidence remains at the status recorded in the linked proofs, experiments, and Lean checks.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. **The unrestricted problem remains open.**

## September 8 consolidation

Reviewed PRs #6–#14 have now been consolidated without replaying stale branch copies of shared ledgers. The first merge integrated #6–#11 and #13; the concrete review defects in #12/#14 were then repaired and integrated as C060–C064/E038–E041.

[Canonical consolidation ledger](research/CONSOLIDATION_2026-09-08.md).

The combined CI gate runs the older established suite, Lean/Python agreement, and every retained continuation regression on one tree.

## Q002 and Q003 are refuted

The modular-synchronization construction gives an eight-state terminal instance whose exact witness language is

    { (1^(6t) 0)^2 : t>=1 }.

Its unique shortest witness has length 14 and exact sufficient budget 7, while `k-2=6`. No budget-six profile-dominated replacement exists, and no strictly shorter profile-dominated replacement exists. Therefore [Q002](research/conjectures/Q002.md) and [Q003](research/conjectures/Q003.md) are **REFUTED**.

The same family gives terminal budgets `2^(Omega(sqrt(k)))`, ruling out polynomial state-count terminal budget bounds but not a larger computable symbolic bound.

[Proof](notes/2026-09-05-modular-synchronization.md), [reproducer](experiments/check_modular_sync.py).

## Exact synchronization and certified recurrent subclasses

The consolidated continuation contains several exact scoped solvers:

- C048–C050: direct binary whole-word synchronization, fragment-specific PSPACE hardness, and fixed-word description lower bounds.
- C051: a five-state NO instance showing that waiting for finite `Necessary(L,D)` emptiness is not a complete general negative semiprocedure.
- C052–C053: exact supplied delimited schemas and a raw bounded-marker certificate.
- C054–C056: finite pending-context normalization and exact target-frontier decisions when no productive marker cycle is reachable from an effective flag target.
- C059: an independent target-local finite-marker-tail pump/checker.

These negative answers are complete only inside their stated certificates. Caps and unsupported formats remain `UNKNOWN`.

## Run normalization: magnitudes are not the main obstacle

C057–C058 show that for terminal accepted words, once the number `r` of maximal homogeneous runs is fixed, run magnitudes can be normalized while preserving run-boundary states, visited states, and the complete suffix-agreement profile. Witness existence with a supplied unary run bound is NP-complete. No unrestricted bound on `r` is known.

C060–C061 strengthen the numerical side further. The uniform code `0->00`, `1->10` embeds every binary instance in a 2k-state bounded-data-run form. More importantly, for **any accepted binary word, even with nonterminal acceptance**, the lengths between occurrences of the final symbol can be contracted while preserving endpoint, visited states, and the full state-pair agreement profile. The reviewed `join_runs` single-pass-iterator bug is fixed and guarded by E041.

These theorems eliminate huge exponent magnitudes as the central missing step. They do **not** bound the number of essential run/marker occurrences.

[Terminal run proof](notes/2026-09-06-run-normalization.md), [broader profile contraction](notes/2026-09-06-run-profile-normalization.md).

## Last-flag spectra versus global minimum violations

The September 7 A017 work exactly decides whether realizable **last-aligned** flag-comparison lengths are bounded. Finite spectra give a valid finite Necessary threshold on the stated boundary-normalized slice; unbounded spectra give pumping certificates, not existential NO verdicts.

C064 sharpens the warning dramatically: a four-state **one-flag terminal instance** has an unbounded realizable last-aligned spectrum while **every bad accepted word has minimum proper violation length exactly one**. Thus long marked comparisons can coexist with a globally constant short obstruction even with only one forbidden ordered state pair.

No C021 nonterminal shortest-word lower bound is imported into the terminal one-flag class.

[Last-flag spectrum](notes/2026-09-07-realizable-lastflag-spectrum.md), [one-flag correction](notes/2026-09-08-oneflag-minimum-gap.md).

## Regular-family verification and shared-lasso arithmetic

C062 classifies a useful verification subproblem exactly:

> Given a regular domain `D`, is **every** word in `D` a witness?

This supplied-family universal verification problem is PSPACE-complete. The corrected lower-bound proof uses a single forbidden pair and explicitly forces equality across all successive synchronized blocks. The executable orbit backend reproduced 43,069 exact backend agreements and 23,781 independently checked counterexamples; deterministic evidence is committed through E039.

This does **not** decide whether a mixed regular family contains some good witness.

C063 shows that any supplied shared-lasso schema remains exactly Presburger-decidable even when separated blocks share exponent variables. On the explicitly **boundary-safe bad subdomain**, the threshold relation `mu(w)>H` for the minimum proper violation length is also Presburger-definable, hence semilinear after projection. The first draft's broader merely-admissible formulation is withdrawn.

[Regular-family proof](notes/2026-09-07-regular-family-complexity.md), [shared-lasso correction](notes/2026-09-08-shared-lasso-presburger.md).

## Logical shortcut audit

The naive Rabin/S2S shortcut has an unresolved orientation step: product propagation acts at the leading end of path words while ordinary binary-tree prefix closure is represented at the trailing end. A direct translation therefore needs an additional cross-end relation such as `y=0x` and must prove it definable or avoid it.

The consolidated audit makes **no** enriched-MSO undecidability claim and no undecidability inference for Subtail.

[Two-ended audit](notes/2026-09-08-two-ended-mso-audit.md).

## Established older foundation

- Top-free path-set semantics and regular countermodel reasoning retain their audited scope.
- Principal binary truncation/context rules, finite-budget predicates, reversal machinery, and an exact two-state decision have Lean-checked core versions.
- Every abstract binary terminal-final BorderAvoid instance has the recorded word-preserving subtype realization.
- A genuine subtype system has a nonregular terminal separating language.
- Flat terminal graphs have an exact finite Presburger skeleton decision.
- The normalized four-state terminal census is complete.

Consult `research/claims.md` before promoting any older result beyond its recorded evidence level.

## Refuted / failed routes to preserve

Do not restart these without a materially new hypothesis:

- Q002's `k-2` profile-domination/budget bound;
- Q003's unconditional strict profile descent;
- any universal polynomial terminal witness-budget bound;
- any state-independent constant bound on simultaneous loop deletions;
- Necessary-language emptiness as a complete general negative semiprocedure;
- ordinary state repetition as justification for loop deletion;
- last-aligned spectrum growth as a proxy for global minimum violation growth;
- a naive S2S translation that silently treats left-prefix as an ordinary tree successor;
- interpreting bounded-run exhaustion or resource caps as unrestricted mathematical `NO`.

## Current frontier

The problem has sharpened to **existence-preserving control of arbitrary nonflat recurrent structure**.

We can now:

1. normalize exponent/run magnitudes exactly once a finite set/number of repeated pieces is fixed;
2. solve arbitrary regular data languages inside supplied finite schemas;
3. coordinate shared exponents arithmetically with Presburger formulas;
4. validate supplied regular families universally in PSPACE;
5. pump substantial target-free recurrent prefixes with finite pending contexts;
6. decide several broader certified target/marker classes.

What is still missing is one of:

- a computable bound on the number of essential runs/markers/schema pieces needed by some witness;
- an effective finite symbolic cover that need not literally bound that count;
- a different terminating exact decision procedure; or
- a genuine undecidability reduction using only the normalized subtype fragment.

The highest-value constructive question is:

> Can every successful nonflat terminal component be normalized into finitely many effectively representable synchronization contexts while preserving all state-coloured suffix obligations in the **same candidate word**?

The most promising adjacent technique source remains nonflat-to-flat reduction for negated string containment, but no transfer to the synchronized family of state-coloured obligations has been proved.

## Research map

- A008 — structure and bounds of minimal witnesses.
- A009 — lower-bound families and candidate-bound destruction.
- A010 — exact subtype-to-automata bridge.
- A011 — converse/expressiveness and exact terminal realization.
- A012 — complete nonexistence certificates and certified subclasses.
- A013 — restrictions shared by actual summary automata.
- A014 — periodic/cap saturation.
- A015 — occurrence-context truncation.
- A016 — fixed-skeleton/shared-exponent arithmetic.
- A017 — bounding/representing essential repeated blocks; central unresolved frontier.
- A018 — backwards formalization from executable Lean decision infrastructure.

## Integration rule

A reusable research step is complete only when it flows through

`investigation -> evidence -> review -> canonical record -> STATE.md frontier update`.

Keep bounded evidence, written proof, independent review, and Lean verification visibly distinct.

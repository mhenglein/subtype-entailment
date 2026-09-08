# Subtail — current research state

Navigation updated: 2026-09-08. Scientific evidence remains at the status recorded in the linked proofs, experiments, and Lean checks.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. **The unrestricted problem remains open.**

## September 8 consolidation

The reviewed PR stack #6–#14 has now been consolidated in two controlled layers without replaying stale branch copies of shared ledgers/trackers. The first layer integrated #6–#11 and #13; the second layer imports only the repaired #12/#14 material after the concrete review blockers were fixed.

[Canonical consolidation record](research/CONSOLIDATION_2026-09-08.md).

The repair layer adds the fixed nonterminal run-profile contraction, exact supplied regular-family verification, boundary-safe shared-lasso arithmetic, the strengthened all-bad-word one-flag result, deterministic evidence publication, and dedicated integration regressions. A dedicated CI job runs the complete continuation suite together on one tree.

## Major consequence: Q002 and Q003 are refuted

The modular-synchronization construction gives an eight-state terminal binary instance whose exact witness language is

    { (1^(6t) 0)^2 : t>=1 }.

Its unique shortest witness has length 14 and exact sufficient budget 7, while `k-2=6`. Any accepted word whose agreement profile is contained in that shortest witness's profile is itself a witness, so neither a budget-six profile-dominated replacement nor a strictly shorter profile-dominated replacement exists.

Therefore [Q002](research/conjectures/Q002.md) and [Q003](research/conjectures/Q003.md) are **REFUTED**. Their earlier bounded searches remain valid historical observations about smaller tested ranges.

The same modular family, using periods `1,...,m`, gives terminal witness budgets at least `2^(Omega(sqrt(k)))`. This rules out every polynomial state-count budget bound but does not rule out a larger computable bound or a symbolic decision method.

[Proof](notes/2026-09-05-modular-synchronization.md), [reproducer](experiments/check_modular_sync.py).

## Exact synchronization and certified recurrent subclasses

### Whole-word synchronization

Binary terminal flags can force multiple regular blocks to be copies of one common word. The direct compiler reduces supplied DFA intersection to a terminal BorderAvoid subclass with an exact finite product solver. This supplies the recorded fragment-specific PSPACE-hardness route and a counting-word family showing that fixed-word skeleton bodies / ordinary concatenation descriptions can require superpolynomial size.

[Implementation](experiments/word_sync.py), [counting family](experiments/counter_intersection.py), [regression](experiments/check_word_sync.py).

### Necessary-budget incompleteness and bounded delimited schemas

A fixed five-state flat terminal NO instance defeats the strategy of waiting for some finite `Necessary(L,D)` automaton to become empty: for every finite budget pair there is a different non-witness that survives that test.

For a supplied bounded delimited-block schema, a reverse padded-convolution machine with persistent equal-tail/hit masks decides arbitrary logical flag relations exactly; the supplied-schema problem is PSPACE-complete. A raw-input certificate derives a finite complete cover for a checkable bounded-marker class.

[Proof](notes/2026-09-06-delimited-convolution.md), [schema solver](experiments/delimited_blocks.py), [raw certificate](experiments/marker_certificate.py).

### Target-frontier and target-tail pumping

The target-frontier construction permits unbounded marker cycles before the first relevant flag target, provided no productive marker cycle is reachable from a relevant target. A powerset keeps all possible early-block observations tied to one common reference tuple.

A separate target-tail construction gives a finite pending-context pump when all flag targets have bounded marker distance to final. Its checker is retained as differential evidence on overlapping certified inputs.

[Target-frontier proof](notes/2026-09-06-target-frontier.md), [implementation](experiments/target_frontier.py), [target-tail proof](notes/2026-09-06-target-local-pumping.md), [implementation](experiments/target_tail.py).

## Run/profile normalization

### Terminal maximal-run normalization

For every defined binary word ending at a terminal accepting state, fixing the number `r` of maximal homogeneous runs is enough to bound and normalize the **run lengths** while preserving the run-letter pattern, run-boundary states, visited-state set, and complete suffix-agreement profile.

Consequently witness existence with a supplied maximal-run bound `R` is decidable by finite symbolic search; with `R` supplied in unary the problem is NP-complete. No computable unrestricted bound on the number of runs required by some witness is known.

[Proof](notes/2026-09-06-run-normalization.md), [normalizer](experiments/run_normalization.py), [bounded-run search](experiments/run_bound_decision.py).

### Nonterminal final-letter profile contraction

The repaired C060–C061 line is broader in a different direction. A uniform `2k`-state code embeds every binary instance into words with data runs of length at most one. Separately, for **any accepted binary word**, even with nonterminal accepting states, treating the word's own final letter as the marker yields an effective contraction of the intervening run lengths that preserves endpoint, visited states, run starts, and the complete ordered state-pair agreement profile.

This again controls numerical magnitudes only after the number of final-letter occurrences is supplied. It does not supply the missing unrestricted occurrence-count bound.

[Integrated proof](notes/2026-09-06-run-profile-normalization.md), [implementation](experiments/run_profiles.py), [regression](experiments/check_run_profiles.py).

## Regular-family and shared-lasso verification

### Supplied regular-family universal verification

C062 classifies the following different problem: given an annotated instance and an unannotated regular domain, decide whether **every** domain member is a witness. This is PSPACE-complete, even with a one-forbidden-pair lower-bound construction. The shared-orbit backend's deterministic regression reproduces 43,069 exact backend agreements.

This is universal verification of a supplied family, not the existential question of whether an arbitrary mixed family contains some good witness.

[Corrected proof](notes/2026-09-07-regular-family-complexity.md), [backend](experiments/regular_family_orbits.py), [deterministic checker](experiments/check_regular_family_orbits_canonical.py).

### Shared-lasso arithmetic

For any supplied shared-lasso skeleton, witness parameter vectors are effectively Presburger-definable. On the explicitly **boundary-safe** bad subdomain, the relation `mu(w)>H` for the minimum proper violation length is also Presburger-definable. The boundary-safety hypothesis is part of the theorem; the equivalence is not asserted for merely admissible words with diagonal, Bad, nonfinal, or empty-suffix failures.

Thus arithmetic inside a fixed synchronization schema is not the current obstacle. The missing theorem is still a finite/existence-preserving coverage result for arbitrary nonflat recurrent structure.

[Corrected proof](notes/2026-09-08-shared-lasso-presburger.md).

## Last-aligned spectra versus global minimum violations

The September 7 A017 continuation decides whether lengths of actual last-aligned flag comparisons are bounded. A finite word action yields an effective unary-regular spectrum. If finite, its exact maximum strengthens the necessary-language certificate on the stated boundary-normalized slice; if unbounded, the procedure returns a pumping certificate.

Unbounded last-aligned spectra are **not** existential NO certificates. The repaired four-state one-flag example sharpens this: its realizable last-aligned spectrum is unbounded, yet **every bad accepted word** has minimum proper violation length exactly one. The all-word statement now has a written proof and a bounded regression through length 16; no nonterminal C021 lower bound is transferred to this terminal class.

[Last-flag spectrum](notes/2026-09-07-realizable-lastflag-spectrum.md), [one-flag separation](notes/2026-09-08-oneflag-minimum-gap.md), [integration regression](experiments/check_consolidation_regressions.py).

## Direct MSO shortcut audit

The naive Rabin/S2S shortcut still has a precise missing step: product propagation acts on the leading symbol of a path word while ordinary binary-tree prefix closure acts at the opposite end. The corrected audit claims only this orientation/definability gap. It withdraws the earlier untraceable enriched-MSO assertion and makes **no** undecidability claim.

[Corrected scope audit](notes/2026-09-08-two-ended-mso-audit.md).

## Shared-word relations and fixed-skeleton arithmetic

Earlier A017 work provides exact finite composition of shared-word templates. Generic iteration of those relations cannot be treated as a decidable black box because two-output append relations already encode Post correspondence; this is not itself a reduction to BorderAvoid.

A016 provides exact Presburger formulas for fixed word skeletons and a finite complete cover for flat terminal candidate graphs. C063 extends the arithmetic observation to shared exponent aliases inside one supplied lasso schema.

[Shared-word composition](notes/2026-09-06-shared-word-composition.md), [recurrent residuals](notes/2026-09-06-recurrent-residuals.md), [flat arithmetic](notes/2026-09-05-terminal-arithmetic.md).

## Refuted ideas / dead ends worth preserving

Do not restart these without a materially new hypothesis:

- Q002's `k-2` agreement-profile / budget bound;
- Q003's unconditional strict profile descent;
- any universal polynomial terminal witness-budget bound;
- any universal constant bound on simultaneous loop deletions;
- the negative semiprocedure that waits for a fixed `Necessary(L,D)` language to become empty;
- identifying an unbounded last-aligned spectrum with unbounded global minimum violation length, even for one flag;
- the old prefix-reachability regular-language formula;
- a universal rigid-word bound from nonmerging runs;
- ordinary state repetition as justification for loop deletion;
- treating `w -> 0w` as an ordinary S2S tree successor without a definability proof;
- reading bounded-search failure or resource exhaustion as mathematical `NO`.

## Current frontier

The central problem has sharpened to **existence-preserving control of arbitrary recurrent structure**.

We can now:

1. normalize run magnitudes exactly once the number of runs/markers/skeleton pieces is fixed;
2. solve arbitrary regular data languages inside supplied bounded schemas;
3. verify supplied regular families exactly;
4. solve shared-lasso arithmetic, including coordinated minimum-violation thresholds on the boundary-safe domain;
5. pump substantial target-free recurrent prefixes using finite pending contexts;
6. decide several broader certified marker/target classes;
7. represent large arithmetic synchronization symbolically.

What is still missing is one of:

- a computable bound on the number of essential runs/markers/schema pieces needed by some witness;
- an effective finite symbolic cover that need not literally bound that count;
- a different terminating exact decision procedure; or
- a genuine undecidability reduction using only the normalized subtype fragment.

The highest-value constructive question remains:

> Can every successful nonflat terminal component be normalized into finitely many effectively representable synchronization contexts while preserving all state-coloured suffix obligations?

A negative result would also be decisive if it supplies a real reduction rather than only showing that a proposed abstraction fails.

## Research map

- A008 — structure and bounds of minimal witnesses.
- A009 — lower-bound families and candidate-bound destruction.
- A010 — exact subtype-to-automata bridge.
- A011 — converse/expressiveness, including exact terminal realization.
- A012 — complete nonexistence certificates and certified subclasses.
- A013 — restrictions shared by actual summary automata.
- A014 — periodic/cap saturation.
- A015 — occurrence-context truncation.
- A016 — exact fixed-skeleton arithmetic and terminal covers.
- A017 — bounding/representing essential repeated blocks; central and unresolved.
- A018 — backwards formalization from executable Lean decision infrastructure.

## Integration rule

A research session is not finished merely when an agent has an answer. It is finished when the reusable part is integrated into shared state:

`investigation -> evidence -> review -> stable record -> STATE.md frontier update`

Keep bounded evidence, written proofs, independent review, and Lean verification visibly distinct.

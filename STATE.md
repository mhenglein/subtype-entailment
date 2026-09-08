# Subtail — current research state

Navigation updated: 2026-09-08. Scientific evidence remains at the status recorded in the linked proofs, experiments, and Lean checks.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. **The unrestricted problem remains open.**

## September 8 consolidation

The reviewed research PR stack #6–#14 has been consolidated onto current main without replaying stale branch copies of shared ledgers/trackers. The integration preserves proof notes, implementations, and independent regressions while keeping later main-branch work authoritative.

[Consolidation record, canonical result map, and held-back work](research/CONSOLIDATION_2026-09-08.md).

The first consolidation merge includes the scientifically surviving material from PRs #6–#11 and #13. PR #12 and PR #14 are deliberately held back pending the concrete repairs recorded in the consolidation note. Their useful observations are not treated as discarded, but their reviewed heads are not integration-ready.

A dedicated CI job now runs the imported continuation regressions together on one tree.

## Major consequence: Q002 and Q003 are refuted

The modular-synchronization construction gives an eight-state terminal binary instance whose exact witness language is

    { (1^(6t) 0)^2 : t>=1 }.

Its unique shortest witness has length 14 and exact sufficient budget 7, while `k-2=6`. Any accepted word whose agreement profile is contained in that shortest witness's profile is itself a witness, so neither a budget-six profile-dominated replacement nor a strictly shorter profile-dominated replacement exists.

Therefore [Q002](research/conjectures/Q002.md) and [Q003](research/conjectures/Q003.md) are **REFUTED**. Their earlier bounded searches remain valid historical observations about smaller tested ranges.

The same modular family, using periods `1,...,m`, gives terminal witness budgets at least `2^(Omega(sqrt(k)))`. This rules out every polynomial state-count budget bound but does not rule out a larger computable bound or a symbolic decision method.

[Proof](notes/2026-09-05-modular-synchronization.md), [reproducer](experiments/check_modular_sync.py).

## Exact synchronization and certified recurrent subclasses

Several integration results substantially enlarge the exact decidable toolkit without closing the unrestricted problem.

### Whole-word synchronization

Binary terminal flags can force multiple regular blocks to be copies of one common word. The direct compiler reduces supplied DFA intersection to a terminal BorderAvoid subclass with an exact finite product solver. This supplies the recorded fragment-specific PSPACE-hardness route and a counting-word family showing that fixed-word skeleton bodies / ordinary concatenation descriptions can require superpolynomial size.

[Implementation](experiments/word_sync.py), [counting family](experiments/counter_intersection.py), [regression](experiments/check_word_sync.py).

### Necessary-budget incompleteness and bounded delimited schemas

A fixed five-state flat terminal NO instance defeats the general strategy of waiting for some finite `Necessary(L,D)` automaton to become empty: for every finite budget pair there is a different non-witness that survives that test.

For a supplied bounded delimited-block schema, however, a reverse padded-convolution machine with persistent equal-tail/hit masks decides arbitrary logical flag relations exactly; the supplied-schema problem is PSPACE-complete. A raw-input certificate derives a finite complete cover for a checkable bounded-marker class.

[Proof](notes/2026-09-06-delimited-convolution.md), [schema solver](experiments/delimited_blocks.py), [raw certificate](experiments/marker_certificate.py).

### Target-frontier and target-tail pumping

The target-frontier construction permits unbounded marker cycles before the first relevant flag target, provided no productive marker cycle is reachable from a relevant target. A powerset keeps all possible early-block observations tied to one common reference tuple.

A separate target-tail construction gives a finite pending-context pump when all flag targets have bounded marker distance to final. Its checker is retained as differential evidence on overlapping certified inputs.

[Target-frontier proof](notes/2026-09-06-target-frontier.md), [implementation](experiments/target_frontier.py), [target-tail proof](notes/2026-09-06-target-local-pumping.md), [implementation](experiments/target_tail.py).

## Universal terminal run normalization

For every defined binary word ending at a terminal accepting state, fixing the number `r` of maximal homogeneous runs is enough to bound and normalize the **run lengths** while preserving:

- the run-letter pattern and run-boundary states;
- the visited-state set;
- the complete suffix-agreement profile.

The construction compresses gaps between sorted repeated counts rather than truncating counts independently. It therefore preserves every flag relation and Bad annotation on the fixed automaton.

Consequently witness existence with a supplied maximal-run bound `R` is decidable by finite symbolic search; with `R` supplied in unary the problem is NP-complete. For each fixed `R` there is an exact polynomial-time enumeration with degree depending on `R`.

**What is not proved:** no computable bound on the number of runs required by some witness of every positive instance is known.

[Proof](notes/2026-09-06-run-normalization.md), [normalizer](experiments/run_normalization.py), [bounded-run search](experiments/run_bound_decision.py).

## Latest main-branch last-flag spectrum result

The September 7 A017 continuation decides whether lengths of actual last-aligned flag comparisons are bounded. A finite word action on states and synchronized pairs yields an effective unary-regular spectrum. If finite, its exact maximum `H` makes `Witness = Necessary(H,0)` on the stated boundary-normalized slice; if unbounded, the procedure returns a pumping certificate.

Unbounded last-aligned spectra are **not** existential NO certificates. The existing seven-state example has unbounded last-aligned comparisons while another comparison supplies a constant short violation.

[Scoped record](research/LASTFLAG_SPECTRUM.md), [proof](notes/2026-09-07-realizable-lastflag-spectrum.md), [results](results/lastflag-spectrum.json).

## Shared-word relations and fixed-skeleton arithmetic

The earlier A017 work provides exact finite composition of shared-word templates and exact universal verification for supplied regular families. Generic iteration of those relations cannot be treated as a decidable black box because two-output append relations already encode Post correspondence; this is not itself a reduction to BorderAvoid.

A016 provides exact Presburger formulas for fixed word skeletons and a finite complete cover for flat terminal candidate graphs. Once a finite schema is known, large arithmetic exponents are manageable. The missing problem is obtaining a complete finite/existence-preserving cover for arbitrary nonflat recurrent structure.

[Shared-word composition](notes/2026-09-06-shared-word-composition.md), [recurrent residuals](notes/2026-09-06-recurrent-residuals.md), [flat arithmetic](notes/2026-09-05-terminal-arithmetic.md).

## Established / strongest prior results

- The top-free characterization has been audited and supports canonical regular countermodels under its stated satisfiability premise.
- Principal binary truncation/context rules have Lean-checked core versions; finite-budget predicates, reversal machinery, and an exact two-state decision are Lean-checked.
- The terminal-final branch is fully expressive for abstract binary terminal BorderAvoid: every `k`-state terminal-final instance has a word-preserving subtype realization on `2k+1` variables.
- A genuine nine-variable subtype system has a nonregular terminal separating language.
- Flat terminal graphs have an exact finite Presburger skeleton decision.
- The normalized four-state terminal census is complete.
- Terminal suffix comparisons have several bounded structural invariants, but none currently bounds arbitrary essential recurrent structure.

Consult `research/claims.md` before treating any older result as formally established; evidence levels differ.

## Refuted ideas / dead ends worth preserving

Do not restart these without a materially new hypothesis:

- Q002's `k-2` agreement-profile / budget bound;
- Q003's unconditional strict profile descent;
- any universal polynomial terminal witness-budget bound;
- any universal constant bound on simultaneous loop deletions;
- the negative semiprocedure that waits for a fixed `Necessary(L,D)` language to become empty;
- the old prefix-reachability regular-language formula;
- a universal rigid-word bound from nonmerging runs;
- ordinary state repetition as justification for loop deletion;
- reading bounded-search failure or resource exhaustion as mathematical `NO`.

## Current frontier

The central problem has sharpened to **existence-preserving control of arbitrary recurrent structure**.

We can now:

1. normalize run magnitudes exactly once the number of runs/markers/skeleton pieces is fixed;
2. solve arbitrary regular data languages inside supplied bounded schemas;
3. pump substantial target-free recurrent prefixes using finite pending contexts;
4. decide several broader certified marker/target classes;
5. represent and solve large arithmetic synchronization symbolically.

What is still missing is one of:

- a computable bound on the number of essential runs/markers/schema pieces needed by some witness;
- an effective finite symbolic cover that need not literally bound that count;
- a different terminating exact decision procedure; or
- a genuine undecidability reduction using only the normalized subtype fragment.

The highest-value constructive question is therefore:

> Can every successful nonflat terminal component be normalized into finitely many effectively representable synchronization contexts while preserving all state-coloured suffix obligations?

A negative result would also be decisive if it supplies a real reduction rather than only showing that a proposed abstraction fails.

## Held-back reviewed work

PR #12's broader nonterminal final-symbol/run-profile contraction is held for an iterable-API fix and notation cleanup. PR #14's regular-family orbit backend reproduced its main test counts, but its accompanying shared-lasso / one-flag proof text needs the scope and reproducibility repairs listed in the consolidation record. Do not use those held-back statements as new premises yet.

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

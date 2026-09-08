# Subtail — current research state

Navigation updated: 2026-09-08. Scientific evidence remains at the status recorded in the linked proofs, experiments, and Lean checks.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. **The unrestricted problem remains open.**

## Latest continuation: encoding-aware synchronous separators

The raw-marker obstruction from the previous continuation is no longer an
obstruction to every delimiter-based method. A finite union-find colouring now
synchronizes transition colours along every pair path rooted at a flag. The
exact compiler maps each transition `a` to `1a` plus an optional `00` separator
and preserves every flagged suffix comparison in both directions.

If synchronized separator classes avoid original cycles, the compiled instance
falls under C053. If terminal synchronization forces an early separator cycle,
C056 can still pump it when it occurs before relevant targets. In particular,
the ten-state `0->00, 1->10` NO example that survives every raw-zero tail bound
has its latent logical-zero separators recovered and is inside the exact C053
class. Thus the previous failure was encoding-sensitive, not a barrier to
finite symbolic separator recovery.

The next preserved obstruction is sharper: a separator cycle forced by terminal
synchronization can be reachable from a relevant flag target. The current C056
wrapper returns UNKNOWN there. The highest-value continuation for this route is
to combine these encoding-aware transition classes with the semantic-tail
pending-context construction so target-recurrent separator cycles are summarized
rather than structurally forbidden.

[Proof and limits](notes/2026-09-08-synchronous-separators.md),
[compiler/deciders](experiments/synchronous_separators.py),
[result](results/synchronous-separators.json).
Written proof + reproducible checks; independent mathematical review pending;
no new Lean theorem is claimed.

## Previous continuation: semantic marker tails

The September 8 A012/A017 attempt decides the fixed-H marker-tail relaxation
by finite shared-reference saturation. Earlier original flag-target STATES
may recur without restriction: the omitted targets are positions before the
last H blocks, not state labels. Weighted joint word actions decide whether
actual last-aligned comparisons have bounded marker count. Finite marker
spectra make this relaxation exact, even with unbounded comparison LENGTHS.

A six-state nonflat NO example with recurrent marker targets is certified at
H=1 although every finite necessary length/gap language is inhabited. Removing
one flag gives the checked witness 1110110. The reset-marker corollary supplies
a complete subclass independent of the older target-cone cycle prohibition.

The closing strengthening fails: the exact code 0->00, 1->10 applied to the
older five-state NO example produces an inhabited relaxation for EVERY H.
Increasing raw marker budgets is therefore not a complete negative procedure.
The synchronous-separator continuation above repairs this specific encoding
obstruction but does not settle target-recurrent separator cycles.

[Scoped record and commands](research/SEMANTIC_MARKER_TAILS.md),
[proof and limitations](notes/2026-09-08-semantic-marker-tails.md),
[results](results/semantic-marker-tails.json).

## September 8 consolidation

The reviewed research PR stack #6–#14 has been consolidated onto current main without replaying stale branch copies of shared ledgers/trackers. The integration preserves proof notes, implementations, and independent regressions while keeping later main-branch work authoritative.

[Consolidation record and canonical result map](research/CONSOLIDATION_2026-09-08.md). [Repaired PR #12/#14 supplement](research/REPAIRED_12_14_2026-09-08.md).

The first consolidation merge integrated the scientifically surviving material from PRs #6–#11 and #13. The concrete review defects that initially held PR #12 and PR #14 back have since been repaired and their distinct results are indexed as C060–C064 and E038–E041. These remain written-proof/reproducer results at the evidence levels stated in the repair supplement; they are not newly Lean-checked and do not resolve Problem 1.7.

A dedicated CI job runs the imported continuation regressions together on one tree, including the repaired #12/#14 checks.

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
3. recover some latent logical separators through exact transition encodings rather than raw symbols;
4. pump target-free and pre-target recurrent prefixes using finite pending contexts;
5. decide several broader certified marker/target classes;
6. represent and solve large arithmetic synchronization symbolically.

What is still missing is one of:

- a complete treatment of synchronized separator cycles reachable from relevant targets;
- a computable bound on essential runs/markers/schema pieces needed by some witness;
- an effective finite symbolic cover that need not literally bound that count;
- a different terminating exact decision procedure; or
- a genuine undecidability reduction using only the normalized subtype fragment.

The highest-value constructive question is now:

> Can target-recurrent synchronized separator classes be composed with one common finite pending-context summary, so every successful nonflat terminal component admits an effective symbolic cover?

A negative result would also be decisive if it supplies a real reduction rather than only showing that a proposed abstraction fails.

## Repaired reviewed work

PR #12's broader nonterminal final-symbol/run-profile contraction now includes the iterable-API repair and list/tuple/generator parity regression. PR #14's regular-family/shared-lasso/one-flag continuation now carries the boundary-safe theorem scope, whole-bad-language argument, corrected lower-bound scope, deterministic evidence publication, and narrowed MSO audit. Canonical records are C060–C064/E038–E041 in [the repair supplement](research/REPAIRED_12_14_2026-09-08.md). Independent mathematical review is still pending where noted.

## Research map

- A008 — structure and bounds of minimal witnesses.
- A009 — lower-bound families and candidate-bound destruction.
- A010 — exact subtype-to-automata bridge.
- A011 — converse/expressiveness, including exact terminal realization.
- A012 — complete nonexistence certificates and encoding-aware certified subclasses.
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

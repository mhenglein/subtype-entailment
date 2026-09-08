# Subtail — current research state

Navigation updated: 2026-09-08; scientific evidence remains at its linked recorded revisions.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work. It answers: **what do we currently know, what has failed, and what is the highest-value unresolved question?**

Detailed proofs and evidence live in `research/claims.md`, approach histories, experiments, Lean, and notes. This file should summarize them without overstating them.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. The unrestricted problem remains open.

## Latest continuation: strategy decision and the single-source target

The September 8 review compares the four recorded routes (terminal small-model
theorem, complete NO certificates / regular containment, undecidability, new
logic or well-structured systems) against the accumulated refutations and
selects the terminal small-model route, executed bottom-up by flag structure.
By C030/C031 nothing is lost by restricting to terminal-final instances.

The first concrete target is the single-source case: all flags leave the
start state. Its witnesses are exactly accepted words none of whose periods
lands on a flagged target state of their own run, i.e. Anderson's
unbordered-word problem with coloured borders. C038 splits a shortest such
witness into two regimes; the remaining obligations are synchronised loop
deletion inside the primitive root with creation analysis, and colour
tracking in the Anderson Theorem 58 argument. Neither is proved here.

Every recorded hard family uses flags in both comparison directions; a
one-directional flag pattern expresses only a colexicographic inequality
between compared blocks, never equality. This is an observation about known
constructions, supported by a complete four-state one/two-flag census and
small samples, not a theorem.

[Note with review, proofs of the two exact forms, and obligations](notes/2026-09-08-strategy-review-and-period-state-form.md),
[checker](experiments/check_period_state_form.py),
[results](results/period-state-form.json).
No new claim or experiment identifier; no evidence level changes; no Lean.

## Previous main-branch continuation: exact realizable last-flag spectra

The September 7 A017 continuation decides whether the lengths of ACTUAL
last-aligned-flag comparisons are bounded. A joint finite word action on
single states and synchronized pairs retains one common word assignment;
terminality bounds the periodic exponent. The resulting length spectrum has
an effective unary-regular presentation. The uncapped analysis computes its
exact maximum H, or returns a pumping certificate proving it unbounded.

A finite spectrum makes Witness exactly Necessary(H,0), strictly extending
the older acyclic pair-graph certificate. A five-state example has H=1 even
though its pair graph has a productive cycle; the solver returns 100.
Unbounded spectra are NOT existential NO certificates. A seven-state NO
example has unbounded last-aligned comparisons but a one-letter detection
bound because another gap supplies a shorter violation in every candidate.

The next distinction is global minimum violation length versus last-aligned
comparison length. Even deciding boundedness of those global minima would
not cover the known NO example defeating every finite necessary budget.
Different comparisons must still be coordinated inside the SAME word.

[Scoped record and commands](research/LASTFLAG_SPECTRUM.md),
[proof and limitations](notes/2026-09-07-realizable-lastflag-spectrum.md),
[results](results/lastflag-spectrum.json).
Written proofs and independent-predicate tests; independent mathematical
review pending, not Lean-checked. The original core replay is byte-identical.
No full repository CI or global link scan was run from the partial snapshot.
Other scientific branches are not merged or promoted by this continuation.

## Earlier main-branch continuation: shared-word relations

The scoped A017 attempt based on `0318ff7` now provides exact finite
composition of shared-word templates and a decidable universal verification
problem: does EVERY instantiation of a supplied family produce a witness?
A violation has the word-equation form w=x d z, d z=z t with regular constraints
locating the flagged states. Classical regular-constrained word-equation
solvability supplies the theoretical decision; the optional Z3 wrapper is
incomplete and retains UNKNOWN, including four recorded infinite positive cases.

A separate finite transition-monoid algorithm completely checks regular
families, including arbitrary nonterminal accepting states. It certifies an
infinite recurrent-target witness family, and returns a bad member for the
broader candidate family WITHOUT implying that no witness exists. Empty
families are explicitly distinguished from inhabited positive certificates.

Generic iteration of these relations cannot be assumed decidable: two-output
append relations already encode Post correspondence. This is not a reduction
to BorderAvoid. The missing step is an effective, complete iteration invariant
specific to actual recurrent suffix obligations. Universal family validation
and exact finite composition do not settle unrestricted witness existence.

[Full proof, dependencies and limitations](notes/2026-09-06-shared-word-composition.md),
[prior residual counterexamples](notes/2026-09-06-recurrent-residuals.md),
[core checks](results/shared-composition.json),
[optional SMT checks](results/shared-composition-smt.json).
New arguments are written and tested, not independently reviewed or Lean-checked.
The partial working snapshot did not support full repository CI/link validation.

Scientific branches remain separate; this update does not merge their proofs
or promote their evidence levels. The [campaign](research/TEN_AGENT_CAMPAIGN.md)
pins those branches and records the Q002/Q003 counterexamples missing from
older main-branch Q records. Do not treat an older OPEN label as support for
using either statement as a premise.

## Established / strongest current results

- The top-free characterization has been audited and supports canonical regular countermodels under its stated satisfiability premise.
- Several witness-shortening rules have written proofs; core binary versions of the principal truncation/context rules are Lean-checked.
- The direct finite-budget predicates, reversal machinery, and an exact two-state decision are Lean-checked. The general executable decision still depends on a missing global bound.
- An actual subtype-to-summary pipeline exists and has independent checks for its implemented interfaces.
- Abstract witness budgets can grow: a one-flag k-state family has exact budget `2k-4` and shortest length `3k-3`; therefore candidate universal bounds must accommodate at least this growth.
- The terminal-final branch is expressive: every k-state terminal-final binary abstract instance has an exact word-preserving subtype realization on `2k+1` variables.
- A genuine nine-variable subtype system has a nonregular terminal separating language.
- Flat terminal graphs admit exact Presburger skeleton formulas and a finite complete cover. The normalized four-state terminal census is complete and leaves no unresolved instance in that finite census.

These statements have different evidence levels. Consult `research/claims.md` before using any one of them as a theorem; not all newer written proofs are Lean-checked.

## Strong evidence / partially established structure

- Actual subtype-derived summaries exhibit absorption structure that is stronger than arbitrary abstract BorderAvoid instances in some branches.
- Context-sensitive truncation rules substantially restrict shortest witnesses, but no known rule yields the required general computable witness bound.
- Fixed-skeleton arithmetic is a viable exact technique once a finite skeleton cover is known. The unresolved difficulty is obtaining such a cover for general nonflat productive terminal components.
- The terminal branch is no longer safely dismissible as an easy regular special case: arbitrary terminal flags can be realized and terminal separating languages can be nonregular.

## Refuted ideas / dead ends worth preserving

Do not restart these without a materially new hypothesis:

- The old prefix-reachability regular-language formula is false; it disagrees on thousands of bounded words and the relevant all-length family is nonregular.
- A universal rigid-word bound from nonmerging runs is false; even two states admit unbounded rigid words.
- State repetition alone does not justify loop deletion; a three-state counterexample exists.
- Bounds as small as `max(0, |K|-2)` or `|K|` are false for general abstract instances.
- Passing bounded searches or CI does not establish nonexistence or a proof of Problem 1.7.

See the relevant A records in `research/README.md` for exact counterexamples and limitations.

## Current frontier

One open route, recorded as [Q001](research/conjectures/Q001.md), asks:

> **Can terminal witnesses in nonflat productive components be normalized into a computably bounded number of essential repeated blocks / skeletons while preserving every border obligation?**

A positive answer would connect the exact fixed-skeleton Presburger machinery to a complete terminal decision procedure. The most relevant workstreams are A016 and A017, informed by the structural shortest-witness work in A008.

Closely related frontier questions:

1. Find a finite join-context summary strong enough to make loop deletion sound and bound essential repeated blocks.
2. Extend the complete flat-terminal skeleton cover to nonflat productive terminal components.
3. Formalize/audit the terminal normalization and arithmetic translation so experimental success is cleanly separated from theorem status.
4. Continue the backwards Lean route: formalize the finite sufficient automaton and exact nonemptiness procedure while keeping the missing global bound explicit.
5. Explore complete NO certificates or saturation only with a precise invariant; failure to find a witness remains `UNKNOWN`.

## Open conjectures

The later profile route is recorded in [Q002](research/conjectures/Q002.md)
and its stronger descent conjecture [Q003](research/conjectures/Q003.md).
Q003 would imply Q002. C044 relates Q002 to the sharp terminal budget bound;
turning that into a subtype decision also needs the exact search and reduction
results at their stated evidence levels. Their main-branch records retain older
OPEN labels; the campaign links later branch refutations awaiting independent
review/integration. Do not use either conjecture as a premise.
C045 supplies a restricted deletion lemma, not a proof of Q003. The failed
single-loop version of Q003 is recorded with the conjecture.

Use the [claim index](research/claims.md#continued-claim-records) for C021–C045
and the [experiment index](experiments/README.md) for later checks. No newer
written result is promoted to Lean status by this navigation update.

Important hypotheses should live in `research/conjectures/` with stable Q IDs. The registry is intentionally small: create a Q record only for hypotheses important enough that multiple researchers or agents may depend on them.

## Research map

- A008 — structure and bounds of minimal witnesses.
- A009 — lower-bound families and candidate-bound destruction.
- A010 — exact subtype-to-automata bridge.
- A011 — converse/expressiveness, now including exact terminal realization.
- A012 — complete nonexistence certificates; not yet tried.
- A013 — restrictions shared by actual summary automata.
- A014 — periodic/cap saturation; not yet tried.
- A015 — occurrence-context truncation.
- A016 — exact fixed-skeleton arithmetic and terminal covers.
- A017 — bounding essential repeated blocks; currently inconclusive and central to the frontier.
- A018 — backwards formalization from an executable Lean decision theorem.

The generated tracker in `research/README.md` contains the authoritative execution status and next step for every A ID.

## Integration rule

A research session is not finished merely when an agent has an answer. It is finished when the reusable part of that answer is integrated into the shared state:

`investigation -> evidence -> review -> claim/approach record -> STATE.md frontier update`

Keep this file short enough that a new researcher can recover the project state in one sitting. Move derivations and chronological detail to the underlying records.

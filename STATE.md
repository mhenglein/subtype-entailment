# Subtail — current research state

Updated: 2026-09-05

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work. It answers: **what do we currently know, what has failed, and what is the highest-value unresolved question?**

Detailed proofs and evidence live in `research/claims.md`, approach histories, experiments, Lean, and notes. This file should summarize them without overstating them.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. The unrestricted problem remains open.

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

The highest-value unresolved question is:

> **Can terminal witnesses in nonflat productive components be normalized into a computably bounded number of essential repeated blocks / skeletons while preserving every border obligation?**

A positive answer would connect the exact fixed-skeleton Presburger machinery to a complete terminal decision procedure. The most relevant workstreams are A016 and A017, informed by the structural shortest-witness work in A008.

Closely related frontier questions:

1. Find a finite join-context summary strong enough to make loop deletion sound and bound essential repeated blocks.
2. Extend the complete flat-terminal skeleton cover to nonflat productive terminal components.
3. Formalize/audit the terminal normalization and arithmetic translation so experimental success is cleanly separated from theorem status.
4. Continue the backwards Lean route: formalize the finite sufficient automaton and exact nonemptiness procedure while keeping the missing global bound explicit.
5. Explore complete NO certificates or saturation only with a precise invariant; failure to find a witness remains `UNKNOWN`.

## Open conjectures

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
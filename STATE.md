# Subtail — current research state

Updated: 2026-09-05

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work. Detailed proofs, exact scopes, and evidence levels live in the claims ledger, approach histories, experiments, Lean, and dated notes.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. The unrestricted problem remains open. A hardness result is not a decision procedure; a failed bounded witness search is not nonexistence.

## Established / strongest prior results

- The top-free characterization has been audited and supports canonical regular countermodels under its stated satisfiability premise.
- Several witness-shortening rules have written proofs; core binary versions of the principal truncation/context rules are Lean-checked.
- Direct finite-budget predicates, reversal machinery, and an exact two-state decision are Lean-checked. The general executable decision still depends on a missing global bound.
- An actual subtype-to-summary pipeline exists and has independent checks for its implemented interfaces.
- The earlier nonterminal abstract family has exact budget `2k-4` and shortest length `3k-3`. Its scope remains distinct from terminal instances.
- Every k-state terminal-final binary abstract instance has an exact word-preserving subtype realization on `2k+1` variables (C030). Together with the infinite-continuation branch, terminal decidability would decide normalized subtype entailment (C031, with the recorded reduction statuses).
- A genuine nine-variable subtype system has a nonregular terminal separating language.
- Flat terminal graphs admit exact Presburger skeleton formulas and a finite complete cover. The normalized four-state terminal census is complete and leaves no unresolved instance in that finite census.

These statements have different evidence levels. Not all newer written proofs are Lean-checked; consult `research/claims.md` and the linked continuation records.

## New results awaiting independent review: C046-C049 / E029

[Proofs and limitations](notes/2026-09-05-terminal-copy-synchronization.md),
[implementation](experiments/terminal_copy.py),
[reproduction](experiments/check_terminal_copy.py),
[certificates](results/terminal-copy.json).

- **Q002 and Q003 are refuted.** An eight-state binary terminal automaton with five flags has exact witness language `{(1^(6t)0)^2 : t>=1}`, unique shortest witness `11111101111110`, and exact budget `7>k-2=6`. All 28 lower-budget splits are exhausted. A profile-dominated replacement would itself be a witness, so neither the low-budget replacement nor strict descent can exist. C030 gives a 17-variable subtype realization, with independently checked regular countermodels.
- **Terminal budgets have super-polynomial lower growth, already on flat graphs.** The LCM family with `k=1+r+sum p_i` has exact `B=(r-1)(lcm(p_i)+1)`. Choosing periods 1 through t proves `B>=2^(Omega(sqrt(k)))`. No polynomial state-count budget bound can work. This does not refute a computable bound or a bounded skeleton with large exponents.
- **Terminal flags can enforce equality of arbitrary regular blocks.** C047-C048 encode an intersection of binary DFA languages as exactly the terminal witnesses `h((u#)^r)`, with polynomial construction size and an exact binary coding. When the component DFAs are supplied, ordinary product reachability decides this constructed subclass.
- **A direct top-free PSPACE-hardness reduction is written.** C049 combines the copy construction, binary coding, and C030 to reduce DFA intersection to bottom/product subtype non-entailment; complement closure gives entailment hardness too. This avoids ambient top. The new reduction and C030 retain their written/audited proof status; there is no claimed upper bound or general decider.

These are written proofs plus executable checks, not Lean proofs or completed independent mathematical review. E029 and the unchanged core border regression pass. Larger numerical examples use the proved formula rather than unreported large-budget searches.

## Refuted ideas / dead ends worth preserving

- The old exact regular prefix-reachability formula is false; an all-length counterexample language is nonregular.
- A universal rigid-word bound from nonmerging runs is false; even two states admit unbounded rigid words.
- State repetition alone does not justify loop deletion. Even multiple loop deletions cannot rescue Q003 in general.
- Flat edge subautomata do not provide a complete witness cover (C035), although richer fixed-word skeletons remain possible.
- The sharp terminal `B<=k-2` bound, its profile-domination formulation Q002, and strict-descent Q003 are false (C046). Their earlier bounded evidence is retained in the conjecture records, not promoted to an all-state theorem.
- More generally, no polynomial successful-budget bound is possible even for flat terminal instances. Do not confuse large repetition counts with an unbounded number of essential blocks.

## Current frontier

> **Can arbitrary terminal witness obligations be represented by a computably bounded collection of skeletons or synchronized block contexts, with exact preservation of every border obligation?**

The new lower bounds redirect the search away from small budget thresholds. Flat arithmetic already handles large exponents, and the new copy subclass has a finite product solution once the common block is identified. The unresolved step is obtaining a finite effective cover or summary for general nonflat productive components and their crossing joins.

Priorities are to extend A016/A017's symbolic coverage, test proposed normalizations against both new synchronization families, independently audit C046-C049 and the terminal-to-subtype transfer, and continue A018's finite-automaton formalization without concealing the missing bound. The existing last-flag and source-pruning NO certificates remain sound restricted tools; their cyclic residuals are not automatically YES or NO.

## Conjectures and research map

[Q001](research/conjectures/Q001.md), the computable essential-skeleton hypothesis, remains open. [Q002](research/conjectures/Q002.md) and [Q003](research/conjectures/Q003.md) are preserved as refuted conjectures. C044's equivalence and C045's local shortening lemma are not refuted.

A008 studies minimal-witness structure; A009 now includes terminal LCM lower bounds; A011 includes terminal realizability and the fragment-specific hardness route; A016/A017 target finite symbolic coverage; A018 targets checked executable components. A010/A013 retain the subtype-summary reduction and absorption results. A012/A014 remain proposed completeness/saturation routes.

The generated tracker in `research/README.md` is the execution-status index. Stable A/C/E/Q IDs distinguish approaches, claims, experiments, and conjectures.

## Integration rule

`investigation -> evidence -> review -> claim/approach record -> STATE.md frontier update`

Keep source papers unchanged and failed arguments visible. Important new mathematical claims remain reviewable on a research branch until integration; neither a closed issue nor passing CI supplies a proof.

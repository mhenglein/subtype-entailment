# Subtail — current research state

Navigation updated: 2026-09-08. Scientific evidence remains at its linked recorded revisions.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. **The unrestricted problem remains open.**

The September 8 consolidation integrates the reusable research artifacts from open PRs #6–#14 onto the September 7 main frontier. It does **not** promote those written proofs to `AUDIT` or `LEAN`. Canonical continuation IDs C046–C064 and their branch-local aliases are recorded in [research/CONSOLIDATED_2026-09-08.md](research/CONSOLIDATED_2026-09-08.md).

## Most important correction: Q002 and Q003 are refuted

Do not use either conjecture as a premise.

C046 gives an eight-state terminal binary instance with exact witness language

    { (1^(6t) 0)^2 : t>=1 }.

Its unique shortest witness has length 14 and exact sufficient budget 7, exceeding `k-2=6`. This refutes Q002's proposed agreement-profile replacement bound. Since the displayed word is already a shortest witness and every profile-dominated accepted word is again a witness of the same modular language, there is no strictly shorter profile-dominated replacement; Q003 is refuted as well.

The same modular family has exact budget

    (r-1)(lcm(p_1,...,p_r)+1)

and yields superpolynomial terminal budgets. A separate C047 family requires an unbounded number of simultaneous equal-state loop deletions, so neither a constant deletion count nor unconditional descent above `k-2` is available.

[Proof](notes/2026-09-05-modular-synchronization.md), [regression](experiments/check_modular_sync.py), [Q002](research/conjectures/Q002.md), [Q003](research/conjectures/Q003.md).

## Latest main-line structural result: exact realizable last-flag spectra

The September 7 A017 work decides whether the lengths of actual last-aligned flag comparisons are bounded. A joint finite word action retains one common word assignment; terminality bounds the periodic exponent. The resulting length spectrum has an effective unary-regular representation and an exact finite maximum or pumping certificate.

A finite last-flag spectrum makes Witness equal to `Necessary(H,0)` for that certified case. An unbounded last-flag spectrum is **not** an existential NO certificate.

The consolidated C064 correction sharpens this warning: a four-state terminal instance with one forbidden pair has an unbounded last-aligned spectrum while **every bad accepted word has minimum proper violation length one**. Different occurrences of the same flag can therefore hide a constant short violation behind arbitrarily long marked comparisons.

## Exact scoped solvers now available

The continuation contains several complete procedures for explicitly stated subclasses. Their negative answers must never be generalized outside those scopes.

- **C048–C050:** direct whole-word synchronization embeds supplied DFA intersection into terminal BorderAvoid and gives PSPACE hardness plus description-size lower bounds.
- **C051:** a five-state NO instance defeats every fixed Necessary budget, proving that waiting for Necessary-language emptiness is not a complete general NO semiprocedure.
- **C052–C053:** supplied delimited schemas are exactly decidable; a raw marker-format class with no productive marker cycle has a finite complete cover.
- **C054–C056:** target-free prefixes can be pumped with pending context, and formatted inputs with no marker cycle reachable from a flag target are exactly decidable.
- **C057–C058:** every terminal accepted word can have its maximal run lengths normalized while preserving the full agreement profile once the run count is fixed; existence with a supplied unary run bound is NP-complete. `NO_WITHIN_RUN_BOUND` is not unrestricted NO.
- **C059:** bounded marker-tail height from every flag target gives a separate target-local exact class.
- **C060–C061:** uniform binary coding embeds the full binary problem in bounded-data-run form, and arbitrary accepted words admit full-profile contraction of the lengths between occurrences of their final symbol. Neither result bounds the number of markers/runs.
- **C062:** verifying that **every** member of a supplied regular family is a witness is PSPACE-complete. This is universal family validation, not mixed-family witness synthesis.
- **C063:** supplied shared-lasso witness sets are Presburger-definable. Minimum-proper-violation threshold growth is Presburger-definable only on the explicitly **boundary-safe** bad subdomain.

All of these are written proofs with reproducible code at their recorded scopes; independent mathematical review remains pending unless a linked older dependency already has a stronger status.

## Shared-word and recurrent frontier

Exact finite composition of shared-word templates and regular-family validation are available, but generic iteration of shared two-output append relations is too expressive to use as a black box. The missing constructive step is still **coverage**:

> Can arbitrary nonflat productive terminal components be reduced to a finite existence-preserving family of controlled schemas, or otherwise given a terminating exact certificate calculus?

A016's fixed-skeleton Presburger machinery solves the arithmetic once a finite skeleton/shared-lasso schema is supplied. C057/C061 eliminate unbounded exponent magnitudes as the primary obstacle once a run/marker count is fixed. What remains unbounded and unsolved is the **number and interleaving of essential recurrent blocks/contexts**.

A promising technique source is the nonflat-to-flat machinery used for a single negated string-containment predicate, but no transfer to the synchronized family of state-coloured suffix obligations has been proved.

## Logical shortcut audit

The naive Rabin/S2S shortcut is incomplete because product propagation acts at the leading end of path words while ordinary prefix closure is represented using the trailing-end successors of the standard binary tree. An exact direct encoding therefore needs an additional cross-end relation such as `y=0x`. The consolidated MSO note makes **no** undecidability or undefinability claim; it records only this missing definability step.

[Two-ended audit](notes/2026-09-08-two-ended-mso-audit.md).

## Established older foundation

The following pre-continuation facts retain their existing evidence levels in `research/claims.md`:

- top-free path-set semantics and regular countermodel reasoning under the stated satisfiability premise;
- the exact forward subtype-to-BorderAvoid bridge and terminal realization results at their recorded scopes;
- direct finite-budget predicates, reversal machinery, and the exact two-state decision, with substantial Lean coverage;
- flat terminal graphs admit exact Presburger skeleton formulas and a finite complete cover;
- several local truncation/context rules are Lean-checked, but none yields the missing global bound.

Consult the claims ledger before treating any item as a theorem; `WRITTEN PROOF`, `AUDIT`, `LEAN`, and `REPRO` are deliberately different evidence levels.

## Refuted / failed routes to preserve

Do not restart these without a materially new hypothesis:

- Q002's `k-2` profile-domination/budget bound;
- Q003's strict profile descent above `k-2`;
- a universal constant bound on simultaneous loop deletions;
- Necessary-language emptiness as a complete general negative semiprocedure;
- state repetition alone as justification for loop deletion;
- rigid-word or very small state-count-only witness bounds;
- last-aligned spectrum growth as a proxy for global minimum violation growth;
- a naive direct S2S translation that silently treats left-prefix as an ordinary tree successor;
- interpreting resource caps, bounded-run exhaustion, or finite tests as unrestricted NO.

## Highest-value next step

The strongest constructive target is now:

> Prove an effective finite existence-preserving cover/normalization for arbitrary recurrent terminal suffix obligations, broad enough to survive whole-word synchronization and the five-state all-budget NO family.

The most discriminating subproblem is a state-coloured copy/containment theorem: decide whether a regular candidate language has a word outside the finite family of state-constrained `x y x` / bounded-overlap patterns induced by its flags, while keeping all occurrences tied to the **same candidate word**. A successful nonflat-to-flat reduction here would plug directly into C063/A016.

An explicit undecidability reduction remains an honest alternative if the Horn/pushdown restrictions can encode the required shared sequence; no such reduction currently exists.

## Research map

- A008 — structure and bounds of minimal witnesses.
- A009 — lower-bound families and candidate-bound destruction.
- A010 — exact subtype-to-automata bridge.
- A011 — converse/expressiveness and terminal realization.
- A012 — complete nonexistence certificates.
- A013 — restrictions shared by actual summary automata.
- A014 — periodic/cap saturation.
- A015 — occurrence-context truncation.
- A016 — exact fixed-skeleton/shared-exponent arithmetic.
- A017 — bounding/normalizing essential repeated blocks; central current frontier.
- A018 — backwards formalization from executable decision components.

## Integration rule

A research session is complete only when reusable results flow through

`investigation -> evidence -> review -> canonical record -> STATE.md frontier update`.

The September 8 consolidation deliberately keeps C046–C064 in a pending-review continuation ledger rather than silently promoting branch-local claims into the established ledger.

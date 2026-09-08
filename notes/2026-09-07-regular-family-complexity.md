# Regular-family validation: PSPACE classification and orbit backend

Date: 2026-09-07. Workstream: A017. Base main: `f663a8d1072fbf21e899f860cba1538a64f3628a`.

**Status:** written proof plus executed regression evidence; independent review pending; not Lean-checked. This does **not** settle unrestricted Problem 1.7.

## Result

For a binary BorderAvoid instance `I` and an unannotated DFA `D`, consider the supplied-family verification problem

> Is every word in `L(D)` a witness of `I`?

This problem is PSPACE-complete. The lower bound already holds for terminal binary instances with no Bad states and one forbidden ordered pair whose two endpoints are each visited exactly once on every candidate word.

This is deliberately a verification theorem, not the existential question `L(D) ∩ Witness(I) != empty`. A mixed family can fail universal validation while still containing a witness.

## PSPACE upper bound

Boundary failures (undefined runs, Bad, nonfinal endpoints, diagonal flags) are regular and checked by a polynomial product graph. Every remaining bad member has a proper flagged agreement. Using the periodic normal form from the preceding A017 work, write such a member as

    x (u v)^e u,

where `v` is nonempty. In the safe product of `I` and `D`, the exponent can be shortened to at most the number `K` of reachable product states; for terminal `I`, terminal nonmerging gives the sharper original-state bound.

For fixed `e`, source/target product states, and the intermediate orbit chain, existence of one common `u` and one common `v` is reachability in a synchronous product carrying at most `e+1` product states. A nondeterministic polynomial-space machine guesses this reachability path while retaining only the current tuple and a polynomial-space counter. Savitch yields PSPACE. Enumerating the polynomially represented outer choices does not increase the space bound.

The important invariant is that every occurrence uses the SAME guessed `u` and `v`; independently chosen representatives would be unsound in view of the recurrent-residual counterexamples.

## PSPACE lower bound

Reduce DFA intersection nonemptiness. For input binary DFAs `A_1,...,A_r`, candidate words encode blocks

    1 w_1 # 1 w_2 # ... 1 w_r #

with `w_i in L(A_i)`. Encode the ternary macro alphabet by the fixed binary code

    0 -> 10,  1 -> 11,  # -> 00.

The candidate automaton enforces code alignment. Add one forbidden pair between the unique boundary entering the first data block and the unique boundary entering the second data block. The final suffix agreement holds exactly when the two corresponding block contents agree; chaining the construction through all blocks yields a bad member exactly when one word is accepted by every input DFA. The construction is polynomial and has one terminal final state. Thus universal validity is PSPACE-hard by complement closure of PSPACE.

The reduction was separately exercised on finite instances by complete candidate enumeration; this is implementation evidence, not the source of the all-length proof.

## Implementation

`experiments/regular_family_orbits.py` implements an exact finite shared-word orbit search. With both caps set to `None` it terminates. The explicit Python breadth-first search can use exponential memory and is **not** itself claimed to be a polynomial-space implementation; the implicit reachability argument above supplies the PSPACE upper bound.

Every returned counterexample is validated with both existing forward and reversed witness predicates. Resource caps return `UNKNOWN`, never `NO`.

The previously executed regression compared this backend with the earlier transition-monoid backend on 43,069 cases, including a 41,472-case exhaustive two-state table/annotation census; all 23,781 returned counterexamples passed both witness predicates. It also included 160 complete finite-family oracles and 100 finite lower-bound construction instances. The detailed result/checker from that run should be integrated separately after the write path is stable.

## Consequence for the frontier

The theorem makes supplied regular-family verification exact and complexity-classified, but it does not synthesize a good member of a mixed family. The unrestricted frontier therefore remains the recurrent-suffix synthesis/normalization problem: find a complete terminating representation of shared word obligations, or an exact negative certificate mechanism. The bad-member bound obtained here must not be reinterpreted as a good-witness bound.
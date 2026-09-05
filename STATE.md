# Subtail - current research state

Updated: 2026-09-05

This is the compressed scientific memory of Problem 1.7. Exact statements,
proof status, experiments, and failed attempts belong in the linked records.
The unrestricted problem is not settled by this repository's current work.

## Latest result: the sharp terminal normalization route is refuted

**C046 (written proof + reproducible counterexample; independent review
requested, not Lean-checked):** an eight-state terminal automaton has exact
witness language `{1^(6a) 0 1^(6a) 0 : a>=1}`, minimum budget seven, and
unique shortest witness `11111101111110` of length 14. Hence the k-2 budget
bound Q002 and the strict-descent conjecture Q003 are false. No shorter
profile-dominated accepted word exists, regardless of deletion strategy.

More generally, r modular unary blocks with periods p_i require identical
positive run lengths. Their minimum budget is

    (r-1)(lcm(p_1,...,p_r)+1),

on `1+sum_i(p_i+1)` states. Periods 1,...,m give budgets at least 2^(m-1) on
(m+1)(m+2)/2 states: no polynomial state-count bound is possible, even for flat
terminal graphs. C030 transfers this growth to normalized subtype inputs.
This family is exactly decidable by an LCM calculation, so it is not an
undecidability result and does not refute a general computable bound.

**C047:** for periods all one, `(1110)^r` needs exactly r equal-state loop
intervals deleted to obtain a shorter profile-dominated word. Thus no
constant number of simultaneous deletions works independently of state count.
This is distinct from C046's genuinely non-shortenable witness.

[Proofs](notes/2026-09-05-modular-synchronization.md),
[claims](research/claims.md#c046), [E031](experiments/README.md#e031),
[Q002](research/conjectures/Q002.md), [Q003](research/conjectures/Q003.md).
The earlier finite samples supporting Q002/Q003 remain observations about
their inputs; they were never all-state proofs.

## Foundations and restricted decisions

The exact problem is subtype entailment over bottom and one covariant binary
product, with arbitrary, possibly infinite type trees. The audited path-set
and pushdown characterization yields canonical regular countermodels under
its satisfiability premise. Finite-tree entailment must not be substituted.

Binary truncation/context lemmas, direct budget predicates, reversal, and an
exact two-state decision have Lean-checked statements. The general executable
budget theorem still exposes its missing global bound as a hypothesis.

The implemented subtype-to-summary bridge has independent checks, not a
complete all-input Lean proof. Later written results include accepting-state
absorption, simplified denial safety, and a decision for witnesses admitting
an infinite safe continuation (C023-C029). A negative answer in that category
is not unrestricted entailment.

C030 realizes every k-state terminal-final binary instance on 2k+1 subtype
variables, preserving words and budgets. Combined with the forward bridge
and the infinite-continuation result, terminal witness existence captures the
remaining normalized problem at the recorded proof levels (C031).

Flat terminal graphs have a finite complete fixed-skeleton cover and an exact
Presburger translation (C033). Practical solver caps remain UNKNOWN. The
four-state terminal census is complete (C034), relying on audited finite-graph
code, not a Lean theorem. Neither flatness nor the small-state result implies
a linear budget bound: C046 is a flat counterexample.

C035-C040 provide nonflat obstructions, terminal nonmerging and bounded
repetition exponents, a last-flag pair-graph decision certificate, and a
forward-closed source-border pruning criterion. Each keeps its hypotheses;
none is a full unrestricted solver. C041-C045 give exact reformulations and
local profile-preserving lemmas, not the now-refuted Q002/Q003 conclusions.

## Failed routes not to restart unchanged

The old exact regular prefix-reach language is false. Universal bounds on all
rigid words are false. Arbitrary equal-state loop deletion is unsound.
Enumerating only flat edge subautomata loses genuine terminal witnesses.
Source-local viability plus a cyclic residual is not sufficient for YES.
Terminal separating languages can be nonregular (C032).

Now also ruled out: the terminal k-2 budget bound, strict descent above that
bound, every polynomial terminal-budget bound, and a universal constant
number of coordinated loop deletions. Their precise scopes matter: local
shortening rules and effective arithmetic descriptions remain useful.

## Current frontier

Find a complete effective representation of witnesses in general nonflat
terminal graphs, while retaining arithmetic synchronization constraints.
A finite existence-preserving skeleton cover remains a candidate, but its
base cases must permit very large exponents and shortest witnesses. It must
not assume Q002, Q003, or a polynomial budget.

The strongest next discriminating question is whether productive cycles in
the unflagged synchronized-pair graph can be reduced to finitely many coupled
arithmetic constraints, with a proved completeness argument. Fixed-skeleton
checkability alone does not supply that reduction. Complete NO certificates
or another computable global bound remain alternatives.

A008/A009 track minimal witnesses and lower bounds; A016/A017 cover arithmetic
and effective skeletons; A012 covers complete NO certificates; A018 keeps the
formal decision obligations explicit. The generated
[approach tracker](research/README.md) remains the authoritative execution
registry. Preserve failures, quantified assumptions, and review status when
updating it.

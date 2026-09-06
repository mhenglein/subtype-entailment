# Subtail - current research state

Updated: 2026-09-06

Unrestricted Problem 1.7 is not settled. Keep arbitrary, possibly infinite
type-tree semantics and all proof/evidence levels explicit. The following
new results have written proofs and reproducible tests, not independent
mathematical review or Lean verification.

## Latest: universal run normalization and target-local pumping

**Proposed C054:** EVERY binary terminal accepted word with r maximal
homogeneous runs can be normalized to length at most

    r^2((k+1)^2+P), with P<=lcm(1,...,k)<=k!,

preserving the exact full agreement profile, visited states, and run-boundary
states. This requires a common compression of sorted run-count gaps; reducing
counts independently can create forbidden agreements. No marker hypothesis is
needed. An exact symbolic profile checker works directly on binary run counts.
A word containing counts 10^80 and 10^80+1 normalizes to 77 letters in the
recorded fixture. The theorem does NOT bound r.

**Proposed C055:** existence with a supplied run bound R in unary is
NP-complete, by C054 and unary-DFA-intersection synchronization. The finite
implementation returns NO_WITHIN_RUN_BOUND, never unrestricted NO. C050's
counting family requires exponentially many runs on polynomial-size inputs,
so a polynomial run-count bound is already excluded.

**Proposed C056:** the automatic marker method now permits productive marker
cycles BEFORE relevant flag targets. It only needs a finite target-to-final
marker height h. A finite pending-context monitor pumps the prefix while
retaining the protected last h blocks. A positive input has a witness with at
most h+K*2^(h-1) markers, yielding a complete schema decision on this enlarged
class. Original-state-only deletion is still unsound; pending guards are
essential. Marker cycles reachable FROM targets remain outside the certificate.

[Proposed claims and E035-E036](research/RUN_NORMALIZATION.md),
[universal normalization proof](notes/2026-09-06-run-normalization.md),
[target-local proof](notes/2026-09-06-target-local-pumping.md).
All limits and actual executed counts are in those records. Tests do not
supply the missing all-input coverage theorem.

## Earlier negative-method obstruction and exact aligned decisions

C051 gives a five-state flat terminal NO instance with nonempty
Necessary(L,D) for EVERY finite budget. Its candidates 1^n 0 1^m 0 fail by
three inequality cases, but m=n+1 moves the only violation beyond any fixed
L,D. This refutes completeness, not soundness, of necessary-budget emptiness.
C030 gives an entailed query on 11 variables and 13 satisfiable normalized
constraints.

C052 exactly decides bounded delimited regular blocks with arbitrary logical
flags/Bad by reverse padded convolution and delayed whole-block guards.
C053 derives complete covers for raw paired or unary marker formats with no
productive marker cycles. C056 weakens that last graph condition. No method
inserts arbitrary new markers: doing so changes witnesshood on the flagged
terminal path 00. [Records](research/DELIMITED.md).

C048-C050 force equality of whole regular-constrained words and provide a
product-decided nonflat class. The explicit reduction gives PSPACE hardness
for terminal BorderAvoid and, through C030, the exact normalized subtype
signature; it is not an unrestricted upper bound. A counting family with one
witness rules out polynomial fixed-word-skeleton and ordinary straight-line
descriptions. [Records](research/WORD_SYNC.md).

C046 refutes Q002 and Q003: eight states require budget seven, with unique
shortest witness 11111101111110. The modular family has exact budget
(r-1)(lcm(periods)+1), already superpolynomial on flat graphs. C047 rules out
a state-independent constant number of coordinated loop deletions.
[Proof](notes/2026-09-05-modular-synchronization.md).

## Foundations retained at their recorded status

The audited path-set/pushdown characterization supports regular countermodels
under its satisfiability premise. Several binary truncation/context lemmas,
direct budget predicates, reversal and the two-state decision are Lean-checked.
The conditional executable theorem still takes a global bound as a hypothesis.

The subtype-to-summary implementation has independent interface checks, not
full all-input formalization. Written C023-C029 supply absorption, denial
safety and the infinitely-extendable witness decision. A NO in that category
is not entailment. C030 realizes arbitrary terminal annotations on 2k+1
subtype variables; C031 connects terminal existence to the remaining
normalized target, at its recorded proof levels.

C033 supplies the flat Presburger decision; C034 completes the four-state
terminal census with audited graph code. C035-C045 include nonflat obstructions,
nonmerging, bounded exponents, restricted source/pair certificates, exact
reformulations, and local cuts, not the refuted global descent conjectures.

## Current frontier

Find a computable bound on the required number of runs, or an exact symbolic
method that avoids bounding it. C054 eliminates uncontrolled exponent size
once r is fixed. The target-local monitor eliminates unrestricted prefix
marker loops when all targets lie in a bounded suffix. Neither addresses
all possible target-reachable cycles and unaligned occurrences.

Do not restart: polynomial witness bounds, Q002/Q003, constant deletion counts,
flat-edge-only coverage, state-only pumping, complete necessary-budget
emptiness, or unrestricted marker insertion. The single negated-containment
result has a narrower scope than our universal state-typed tests; see the
[literature check](notes/2026-09-06-string-theory-boundary.md).

A012 tracks complete NO methods; A017 tracks normalization and finite covers.
A008/A009 preserve lower-bound history; A011 tracks exact reductions; A018
keeps formal proof obligations explicit. The [tracker](research/README.md)
records execution status; closing a PR or passing tests is not a theorem.

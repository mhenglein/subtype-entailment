# Target-return elimination: route outline

Base: b79bc02d5a669fde60484a463941b16e03805050. Workstream A017.
Date: 2026-09-13. Initial route retained; outcome appended below.
No unrestricted solution asserted.

## Exact final objective
Decide whether any accepted word of a finite binary terminal deterministic
instance avoids every flagged suffix-prefix comparison, preserving arbitrary
infinite-tree subtype semantics via the repository's existing bridge.

## Attempt
Replace universal last-target uniqueness with several source-sensitive suffix
constraints. If a forbidden comparison aimed at target label t remains
forbidden whenever its synchronized right run returns to t, all occurrences
of that target collapse to its last occurrence. Retain one shared full word.

For a last target, a productive target-free tail cycle gives an original
witness by C077's period argument. Otherwise all such tails are finite and
have length at most the current state count minus one. For every possible
tail, intersect the candidate language with a deterministic monitor forbidding
that tail only at source states forbidden into its target. Require the same
literal tail at the actual terminal cut. Remove that entire target column
only after a synchronized-return certificate. Iterate; original target labels,
not expanded monitor states, decrease.

## Termination obligation being proved
The fixed-tail monitor can retain the state at the start of its longest
matching prefix, not independent histories for every shorter match. A K-state
candidate automaton and a length-m tail then need at most Km+1 states.
The recursive elimination depth is at most the original number r of target
labels. The intended uniform bound is 2*K^(2^r), for K>=2.

## Outstanding global implication
The return-preservation certificate need not hold for arbitrary flags.
A complete finite cover or alternative handling of every failing branch
would still be required for the unrestricted problem. Test this explicitly
against the existing positive modular example and negative marking barrier.
Do not identify a new decidable class with global completeness.

## Opposing route and literature boundary
A failed return is a precise way for an older target obligation to disappear
at a later legal match. It is a candidate mechanism for computational encoding,
not such a reduction. The 2025 single-negated-containment result does not by
itself decide arbitrary conjunctions of source-sensitive suffix obligations;
its future-work section explicitly distinguishes multiple predicates.

## Recorded outcome

The Km+1 filter and return-closed inheritance arguments yield a native finite
recursive decision for the certified class, with bound 2*k^(2^r). The five-state
legal-repetition example and eight-state recursive negative example are handled
although the prior target-anchor wrapper returns UNKNOWN. A fully realized
modular counterexample refutes unconditional last-per-target elimination.
Original target groups, overlapping occurrences and complete branch coverage
are tested explicitly. The general return-loss branch remains open.

[Full proof and scope](2026-09-13-target-return-elimination.md),
[canonical C079/E051 record](../research/TARGET_RETURN.md).
Written proof plus reproducible code/certificate checks, not independent
mathematical review or Lean. Execution metadata and ownership are unchanged.

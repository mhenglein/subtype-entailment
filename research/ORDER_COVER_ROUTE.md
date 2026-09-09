# Route outline: guarded order constraints and recurrent coverage

Date: 2026-09-09. Input base: 05b20ee73841d0e7105a44beb761e553a7081a8d.

Final target: a total decision procedure for terminal binary BorderAvoid with
its original admissibility, diagonal and empty-suffix semantics. The current
attempt does NOT assume a bound on word length, run count or recurrent visits.

Constructive route (backward and forward):
1. Express suffix violations on a finite symbolic block description as guarded
   order constraints on common block values. For homogeneous unary blocks,
   equality of following blocks is an equality-only guard. This is exact.
2. DISCHARGED FOR THE STATED CLASS: supply a complete terminating proof calculus for that constraint language,
   including congruence domains; reconstruct compact witnesses or finite NO
   certificates. Targeted here: arbitrary number of supplied serial blocks,
   each with a positive count in one arithmetic progression, with arbitrary
   entry/interior flag roles. This strictly generalizes the previous three-
   block finite census and covers modular synchronization lower bounds.
3. OPEN (not discharged by the new backend): obtain an existence-preserving finite cover of arbitrary recurrent
   terminal automata by this or another decidable constraint language. Neither
   number of blocks nor congruence periods may be guessed complete. General
   annotations can depend on phase, and arbitrary word blocks need shared
   word values rather than counts. No inference from step 2 to 3 is assumed.
4. Once 3 is established, compose with the recorded C030/C031 semantic bridge
   at its existing proof status. No new semantic transfer is claimed.

Opposing route: reduce accepting computation of a two-counter machine to
existence. Regular syntax can constrain control/zero tests; the missing gadget
must enforce counter updates at every adjacent configuration, with an arbitrary
future computation. The familiar two-copy unary error detectors can express
such errors when arbitrary trailing context is allowed. Original BorderAvoid
anchors the second comparison at the final suffix. Do not import universality
of general backreferences without proving this trailing-context elimination.

Discriminators: exact weak-order oracle on small chains; all 4096 three-stage
annotations; direct DFA/suffix predicates; known equal-length modular witnesses;
regular raw-language tests for the compiler; negative checks for non-coprime
congruences. A successful restricted result is one complete backend, not an
end-to-end resolution. A repeated-context cover or a terminal-anchored update
gadget remains the genuinely open implication.

Results: notes/2026-09-09-guarded-order-and-terminal-anchor.md gives the uniform
order/domain proof and an explicit two-copy trailing-context computation-error
reduction. The reduction is to the nearby pattern problem, not to BorderAvoid.
The exact terminal-anchor elimination remains open. No original problem status
changes. Existing notes and both directions of investigation remain retained.

# Copy-only cycle acceleration: route and discriminating obstruction

Date: 2026-09-10. Base: 2e431ff3d74d3ab1268866f86e24fd835ffe7fda.
Workstreams A017/A011; source-capture C067/C068 is the current parallel baseline.
Status: exploratory end-to-end outline; this is not a general decision proof.

## Exact goal

For binary terminal BorderAvoid, either supply an effective finite
existence-preserving symbolic cover, or a genuine undecidability reduction.
The current attempt studies a repeat cycle with one unchanged shared word.
Arbitrary trees in Problem 1.7 are retained through the existing C030/C031
bridge, not replaced by finite trees.

## Proposed chain

1. Build an explicit deterministic binary terminal instance that forces every
   earlier block to equal one final block, with unboundedly many early blocks.
2. Prove its all-length witness language, independently check cuts, and inspect
   its length series before assuming rational counting can extend from C065.
3. For a primitive block B, replace unbounded iteration by the equation UB=BU,
   U nonempty. This must retain the SAME B at every occurrence.
4. Implement an exact finite action-orbit decision for regular restrictions on
   both B and the whole output, avoiding a guessed copy bound.
5. OPEN: show that arbitrary instances admit a finite cover by such accelerated
   relations or some richer terminating class. Neither this family nor C068
   supplies that coverage theorem.

## Construction contracts

All automata, flags, domains and endpoints are explicit in the companion note.
The family is B^m 01 B where B=E(u)00, E(0)=10,E(1)=11, u nonempty, m>=1.
The primitive-block guard is proved, not assumed for arbitrary words.
A filter solver uses a finite graph of a data-DFA state and the complete action
of E(u) on the output-domain DFA. Copy-count search is a finite state orbit.
All caps return UNKNOWN; a failed instance recognition is not NO.

## Necessary target vs stronger substitutes

Existence does not require rational length series or a semilinear length set.
Nor must it retain all source visits or all agreement profiles. The action
replacement keeps the equal-block family and its regular restrictions, not
arbitrary contextual substitutability. The compiler is for a supplied family,
not a recognizer claiming every terminal input has this form.

## Opposing route

Unbounded copy count times variable block length produces multiplication in
length projection. Test whether independent factors can be reused between two
zones and combined, rather than inferring undecidability from that product.
Generic two-output append iteration remains PCP-capable. Copy-only acceleration
must not be extended to variable increments without an additional proof.

## Evidence and review

Check arbitrary raw words against both original predicates, all short accepted
paths, exact divisor coefficients, all small regular filters, complete finite
language filters, and nonprimitive commuting counterexamples. No new Lean work
is planned; the all-length arguments require independent mathematical review.

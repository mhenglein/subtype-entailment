# Three-way regular-middle cut certificates

Date: 2026-09-08. Continues the regular-decoration barrier by extracting its
all-length NO proof into a reusable finite certificate rule.

**Status: written proof + exact finite verifier; independent mathematical review pending; not Lean-checked. This is a sufficient NO rule, not a complete calculus and not a solution of Problem 1.7.**

## 1. Rule

Fix distinct binary letters `a,b`. Let `M` be a regular language satisfying

1. every nonempty word of `M` begins with `a`;
2. on the terminal candidate automaton, every `u in M` acts as a loop on one
   distinguished control state `q`.

Suppose the complete boundary-normalized candidate language is exactly

    a^n b u a^m b a

with `n>=0`, `m>=1`, and `u in M`.

Assume the deterministic run has the following stable controls:

- `s0` is the initial state;
- after one or more leading `a`s the state is `s1`;
- reading `b` from either `s0` or `s1` reaches `q`;
- `M` loops `q` back to `q`;
- after one or more trailing `a`s the state is `r`;
- the final `b a` reaches the unique terminal final;
- the flag relation contains

      (s0,r), (s0,q), (s1,q).

Then the candidate language has no witness.

## 2. All-length proof

Write a candidate as

    w = a^n b u a^m b a.

Because `m>=1` and every nonempty `u` begins with `a`, the symbol immediately
after the first `b` is always `a`: if `u` is nonempty this is its first symbol;
if `u` is empty it is the first symbol of the trailing `a^m` block.

There are three exhaustive arithmetic cases.

### Case n < m

Use source cut `i=0`. In the trailing `a^m` block choose the target cut after
exactly `m-n` trailing `a`s. The target suffix begins

    a^n b a.

The source suffix begins with the leading

    a^n b a

for the observation above. The source state is `s0`; because at least one
trailing `a` has already been consumed, the target state is `r`. Hence the flag
`(s0,r)` witnesses a forbidden prefix agreement.

### Case n = m

Use source cut `i=0` and target cut at the start of the trailing `a^m` block.
Both suffixes begin

    a^n b a.

The states are `(s0,q)`, which is flagged.

### Case n > m

Use source cut `i=n-m`, inside the leading `a` block, and target cut at the
start of the trailing `a^m` block. Both suffixes begin

    a^m b a.

Because `n-m>=1`, the source state is the stable leading state `s1`; the target
state is `q`. The flag `(s1,q)` witnesses the violation.

Thus every candidate is bad. The argument is independent of the length or
internal recurrent structure of `u`; only the two finite regular premises on
`M` matter. QED.

## 3. Why the proof object is finite

`experiments/three_way_cut_certificate.py` verifies every premise effectively.

### Exact candidate-language equality

The family `a* b M a+ b a` is represented by an epsilon-NFA formed by
concatenating the regular pieces. The verifier explores the product of the
terminal candidate DFA with epsilon-closed subsets of this NFA. A reachable
acceptance disagreement gives a concrete symmetric-difference word. Exhaustion
proves exact language equality for all lengths.

### Middle first-letter condition

The verifier asks whether the middle DFA has any accepting path after consuming
`b` as its first symbol. This is ordinary finite reachability.

### Middle control-loop condition

It explores the product of the middle DFA with the terminal automaton starting
at `(middle.start,q)`. Every accepting middle state must pair with `q`. This
checks `delta(q,u)=q` for every `u in M`, including arbitrary recurrent words.

### Stable control and flag conditions

The remaining hypotheses are direct transition/flag table equalities. Therefore
`VERIFIED_NO` is an all-language finite certificate verdict. Bounded enumeration
is used only as an independent regression of the implementation.

## 4. Barrier instance recovered exactly

For the six-state regular-marking barrier use `a=0`, `b=1` and

    M = (0+ 11)*.

A three-state partial DFA recognizes M:

- state 0: block boundary, accepting; `0 -> 1`;
- state 1: inside `0+`; `0 -> 1`, `1 -> 2`;
- state 2: after first `1`; `1 -> 0`.

The terminal automaton controls are

    s0=0, s1=1, q=2, r=3, pre-final=4, final=5,

and the required flags are exactly

    (0,3), (0,2), (1,2).

So the six-state arbitrary-regular-middle NO proof is an instance of the generic
finite rule, not a one-off handwritten argument.

## 5. Significance and limit

This is the first installed NO certificate in this continuation whose
termination does **not** come from a bounded comparison length, bounded gap,
bounded marker count, or candidate-covering finite decoration. It covers an
arbitrary recurrent regular middle by separating finite control from two unary
anchor parameters and resolving their order by a finite Presburger case split.

The rule is still narrow. It has one pair of unary anchors, one regular middle,
and three fixed cut selectors. Completeness is not claimed.

The natural next generalization is a **finite affine cut-selector certificate**:

- a regular skeleton with finitely many parameterized unary/periodic blocks;
- a finite Presburger partition of the parameter domain;
- on each cell, affine source/target cut positions;
- finite-state proofs that the selected cuts have a required flag and equal
  target-length prefix.

If verification of such certificates stays effective, the central A012
question becomes whether every terminal NO instance admits a finite selector
cover. The regular-decoration barrier no longer blocks this route because the
certificate is allowed to choose different violating cuts in different
arithmetic regions rather than preserving one finite tail abstraction.

## 6. Reproduction

Run

    python3 experiments/check_three_way_cut_certificate.py

The checker verifies the infinite-language certificate exactly, independently
compares the barrier DFA with the family parser on all binary words through
length 14, confirms that deleting any one of the three required flags invalidates
the proof object, and rejects an enlarged middle language.

Implementation: `experiments/three_way_cut_certificate.py`.
Checker: `experiments/check_three_way_cut_certificate.py`.

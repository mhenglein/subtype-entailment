# Three-way regular-middle cut certificates

Date: 2026-09-08. Continues the regular-decoration barrier by extracting its
all-length NO proof into a reusable finite certificate rule.

**Status: written proof + exact finite verifier; independent mathematical review pending; not Lean-checked. This is a sufficient NO rule, not a complete calculus and not a solution of Problem 1.7.**

## 1. Rule

Fix distinct binary letters `a,b`. Let `M` be a regular language such that every
nonempty word of `M` begins with `a`. Suppose the complete boundary-normalized
candidate language is exactly

    a^n b u a^m b a

with `n>=0`, `m>=1`, and `u in M`.

Assume the deterministic run has stable leading controls:

- `s0` is the initial state;
- after one or more leading `a`s the state is `s1`;
- reading `b` from either `s0` or `s1` reaches the same anchor state `q0`.

The accepted middle words need **not** all loop `q0`. Let

    E = { delta(q0,u) : u in M }

be their finite set of effects. For every `q in E`, require:

- reading one or more trailing `a`s from `q` stabilizes at a state `r_q`;
- from `r_q`, the final `b a` reaches the unique terminal final;
- the flags contain

      (s0,r_q), (s0,q), (s1,q).

Then the candidate language has no witness.

The earlier one-control rule is the special case `E={q0}`.

## 2. All-length proof

Write a candidate as

    w = a^n b u a^m b a

and put `q=delta(q0,u)`. Since `m>=1` and every nonempty `u` begins with `a`,
the symbol immediately after the first `b` is always `a`: if `u` is nonempty
this is its first symbol; if `u` is empty it is the first symbol of `a^m`.

There are three exhaustive arithmetic cases.

### Case n < m

Use source cut `i=0`. In the trailing `a^m` block choose the target cut after
exactly `m-n` trailing `a`s. The target suffix and source suffix both begin
`a^n b a`. At least one trailing `a` has been consumed, so the target state is
`r_q`. The flag `(s0,r_q)` witnesses the violation.

### Case n = m

Use source cut `i=0` and target cut at the start of the trailing `a^m` block.
Both suffixes begin `a^n b a`; their states are `(s0,q)`, which is flagged.

### Case n > m

Use source cut `i=n-m`, inside the leading `a` block, and target cut at the start
of the trailing `a^m` block. Both suffixes begin `a^m b a`. Since `n-m>=1`,
the source state is `s1`; the target state is `q`. The flag `(s1,q)` witnesses
the violation.

The chosen `q` depends on `u`, but it lies in the finite set E and the verifier
checks all members of E. Thus every candidate is bad. QED.

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

### Finite middle effects

It explores the product of the middle DFA with the terminal automaton starting
at `(middle.start,q0)`. Every accepting middle-product state contributes one
endpoint `q` to E. Finiteness is immediate. Undefined endpoints invalidate the
certificate. Each realized q is then checked for trailing stabilization, the
forced terminal `ba`, and all three flags.

Hence `VERIFIED_NO` is an all-language finite certificate verdict. Bounded
enumeration is used only as an independent regression of the implementation.

## 4. Barrier instance recovered exactly

For the six-state regular-marking barrier use `a=0`, `b=1` and

    M = (0+ 11)*.

A three-state partial DFA recognizes M:

- state 0: block boundary, accepting; `0 -> 1`;
- state 1: inside `0+`; `0 -> 1`, `1 -> 2`;
- state 2: after first `1`; `1 -> 0`.

Here E is the singleton `{2}`. The terminal automaton controls are

    s0=0, s1=1, q=2, r_q=3, pre-final=4, final=5,

and the required flags are exactly `(0,3), (0,2), (1,2)`. Thus the six-state
arbitrary-regular-middle NO proof is an instance of the generic finite rule.

## 5. Significance and limit

This is the first installed NO certificate in this continuation whose
termination does **not** come from a bounded comparison length, bounded gap,
bounded marker count, or candidate-covering finite decoration. It covers an
arbitrary recurrent regular middle by separating finite control from two unary
anchor parameters and resolving their order by a finite Presburger case split.
The generalized verifier additionally permits finitely many different middle
transition effects rather than demanding one common reset state.

The rule is still narrow: one pair of unary anchors and three affine cut
selectors. Completeness is not claimed.

The natural next generalization is a **finite affine cut-selector certificate**:

- a regular skeleton with finitely many parameterized unary/periodic blocks;
- a finite Presburger partition of the parameter domain;
- on each cell, affine source/target cut positions;
- finite-state proofs that the selected cuts have a required flag and equal
  target-length prefix.

A016's fixed-skeleton Presburger compiler already supplies exact state/letter
formulas for parameterized fixed-word blocks. The missing ingredient is a
regular-piece interface allowing such affine selectors to cross recurrent
regular middles without expanding them into fixed words.

If every terminal NO instance admitted a finite selector cover, dovetailing the
verifier with positive witness enumeration would decide terminal BorderAvoid.
The regular-decoration barrier does not block this route because the certificate
may choose different violating cuts in different arithmetic regions.

## 6. Reproduction

Run

    python3 experiments/check_three_way_cut_certificate.py

The checker verifies the infinite-language certificate exactly, independently
compares the barrier DFA with the family parser on all 32,767 binary words
through length 14, confirms that deleting any required flag invalidates the
proof object, and rejects an enlarged middle language.

Implementation: `experiments/three_way_cut_certificate.py`.
Checker: `experiments/check_three_way_cut_certificate.py`.
Recorded result: `results/three-way-cut-certificate.json`.

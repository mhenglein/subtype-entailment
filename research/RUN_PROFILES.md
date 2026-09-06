# Binary normal forms and run profiles: proposed C057-C059 / E036

Date: 2026-09-06. Base: PR #10 (`6a13dfb`).
**Status:** written proofs and reproduced checks, independent review pending.
Not Lean-checked. No unrestricted decision for Problem 1.7 is claimed.

## C057 - Full expressive power with data runs of length at most one

The uniform code C(0)=00, C(1)=10 gives an exact 2k-state reduction preserving
witnesshood. All flags/Bad remain on original states at even boundaries; helper
states are unannotated. Encoded words end in zero and contain no consecutive
ones. Thus the general terminal problem is already present in this bounded-run
normal form. This differs from unsoundly appending a new final delimiter.

Separately, terminal-final/last-bit slices are word-preserving without adding
states. A wrapper runs the existing frontier solver over these exact slices,
with global bit exchange as needed. It never converts an unresolved slice to NO.

## C058 - Unconditional full-profile run contraction

For ANY binary DFA (terminality is unnecessary), write an accepted nonempty
word as a^n_0 b ... a^n_(r-1) b, where b is its last symbol. Complete the unary
a-transition with an absorbing sink; let P be the LCM of its cycle lengths,
h=k+1 and T=(k+1)^2. Fix every distinct length <=T. Above T, keep sorted gaps
below h and replace larger gaps g by h+((g-h) mod P).

The resulting increasing contraction preserves every unary-run endpoint,
visited state, and full state-pair suffix-agreement profile. Consequently it
preserves witnesshood simultaneously for all flag relations and Bad sets on
the same DFA. With d distinct lengths the new word has length at most

    r[(k+1)^2+d(k+P)+1].

The exact pair-orbit proof retains short differences, weak order, residues,
and small minima. Order and residues alone are insufficient: the note supplies
a six-state counterexample. A recurrent-target witness shrinks from 1,421 to
135 letters while retaining its entire profile; this does not give a complete
solver for that recurrent class.

## C059 - Marker-count equivalence and a necessary large lower bound

Put Lambda_k=lcm(1,...,k). A computable existential marker bound M(k) would
supply the word bound

    M(k)[(k+1)^2+M(k)(k+Lambda_k)+1].

Such a bound exists iff terminal witness existence is decidable. C057 shows
that the full difficulty remains even when every data run has length zero or
one. Applying that code to C046 gives exact minimum marker count
r(lcm(p_i)+2), which is superpolynomial on quadratic-state families. No
computable bound on M(k) has been proved here.

[Complete definitions, proofs, counterexamples and limitations](../notes/2026-09-06-run-profile-normalization.md).

## E036 - Reproduction

```sh
python3 experiments/check_run_profiles.py
```

[Implementation](../experiments/run_profiles.py),
[checker](../experiments/check_run_profiles.py),
[result](../results/run-profiles.json).

75 unary maps; 448,386 tail-orbit checks; 6,753 two-state words; 137 long
contractions; 640 large-integer vectors; 50,800 last-bit slicing word checks;
20,320 encoding comparisons and 81,760 raw encoded-language checks; 160 complete
acyclic wrapper oracles (105 YES/55 NO); four exact canonical path checks.
Tests and all-length proofs have separate roles. No full CI or Lean is claimed.

## Remaining target

Bound or represent the unbounded SEQUENCE of data-run values and its later-block
equality guards. Numerical run lengths have a profile-preserving contraction;
repeated targets need not be excluded for that theorem. But the number of runs
is not bounded, and its bounded-data special case already encodes the whole
terminal problem. A finite pair signature alone does not solve sequence coverage.

# C023-C024: actual summary absorption and a denial-free decision

Date: 2026-09-04. **WRITTEN PROOF + REPRO; not Lean-checked.** The construction argument refers to the normalization and summary code at b8b8457245b693c760a52b5f445996c0fd2f8b0d. The automaton theorem is independent; transfer to subtype entailment relies on the audited forward bridge. No literature-priority claim.

## C023: joint invariant of transitions, finals, and flags

Write BF for forced product roots. Every normalized lower product x*y<=z adds pushes x --0--> z and y --1--> z and places z in BF. Upper products add pops and variable inequalities add epsilon rules. Thus every push target in W is in BF; every pop source in Wrev is in BF.

In `build_pop_summary`, letter edges are added only for base pops. Saturation adds epsilon edges, not new letter edges. Every letter-edge source in the A/Wrev summary is therefore in BF. Each deterministic A subset is epsilon-closed.

A class q is final exactly when A(q) is disjoint from BF. No member of such A(q) can have an outgoing letter edge. Hence A(delta(q,a)) is empty for either letter a. It remains empty after all later letters. Since G(p,q) iff B(p) intersects A(q), every positive-length descendant of a final is final and has an empty incoming flag column.

Denial tracking adds a safety component but does not change this proof. Thus C023 also holds with bottom denials.

The C021 five-state family violates the invariant: its sole final has a 1-edge to a nonfinal. C020 also violates it: final 2 has successors 1 and 4 that are nonfinal (and carry incoming flags). Neither is a raw output up to annotated-automaton isomorphism. No claim excludes other encodings or language-equivalent realizations.

## C024: exact Bad-free absorbing subclass

Let I be a total finite annotated DFA over at least two distinct letters a,b, with no Bad states. Let Z be the final states whose incoming flag columns are empty. Assume every successor of every final belongs to Z.

**Theorem:** witness existence is equivalent to reachability of Z while avoiding diagonal-flagged states. A nonempty k-state instance has witness length at most 2k-1 and sufficient budget at most k-1; sharpness is not claimed.

Necessity: a witness avoids diagonals and ends at a final. Every one-letter extension is defined and leads into Z, which has no diagonal flag. Hence Z is diagonally safely reachable. This extension argument requires totality and absence of Bad.

Sufficiency: choose a shortest diagonal-safe path v to Z and n=|v|<=k-1. If n=0, epsilon is a witness. Otherwise take w=v a^n b. Every state at positions at least n stays in Z, so no flag can target any such position. Diagonals before n were excluded. For a strict pair i<j<n, put d=j-i, with 1<=d<=n-1. Suffix agreement would equate the final b at position 2n with the letter at 2n-d, inside the appended a block. This is impossible. Thus w is a witness.

The suffix a^n b has no earlier occurrence: any earlier occurrence must end at an earlier b, which is inside v of length n; the suffix itself has length n+1. Therefore Sufficient(w,n,0) holds and the bounds follow.

The decision deletes diagonal-flagged states and searches the finite graph for Z. Failure proves NO, success returns the explicit padded word. A guarded implementation returns UNKNOWN if the hypotheses fail.

## Denial-free normalized subtype consequence

Without BottomDenial constraints, the actual summary DFA is total, binary, and has no Bad states; C023 supplies absorption. C024 therefore decides the normalized ProductLower/ProductUpper/VariableLeq fragment, using the existing forward bridge. The state count is the number of summary classes, not subtype variables. General syntax normalization and a Lean verification of the bridge remain separate.

With denials, padding may violate safety. For example x<=u*v together with u<=bottom and v<=bottom permits a root at x but no safe child product. No unrestricted decision follows by dropping the Bad-free assumption.

## E018 evidence

Run `python3 experiments/check_summary_absorption.py`. The independent NFA implementation generates 400 denial-free systems, seed 2026090421, with two through five variables. All satisfy C023. The largest paired DFA has eight states; C024 yields 281 YES and 119 NO. Positive words pass forward, reversed, and direct sufficient checks; negative answers independently exhaust Necessary(0,0). Both abstract obstructions are rejected by the subclass guard. This is not a rerun of the full bridge or its denial saturation; the general claims rest on the written proofs.

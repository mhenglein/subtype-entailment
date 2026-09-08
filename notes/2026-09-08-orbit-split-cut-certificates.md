# Orbit/residue-split three-way cut certificates

Date: 2026-09-08. Continues the finite symbolic NO direction after the installed
three-way rule in `three_way_cut_certificate.py`.

**Status: written proof + exact finite verifier + reproducible regression;
independent mathematical review pending; not Lean-checked. Unrestricted Problem
1.7 remains open.**

## 1. Why the previous rule is stronger than necessary

The installed three-way verifier certifies candidate languages of the form

    a^n b M a^m b a,   n>=0, m>=1,

but its automatic synthesis requires every state in the positive leading
`a`-orbit to take `b` to one common anchor. The cut proof itself never uses a
common anchor. Once the actual middle endpoint `q` is fixed, the three cases
only compare `n` and `m`.

This continuation therefore splits the candidate family by the finite control
state reached after the leading power. It also allows `b` to be available only
on some leading orbit states, so the admissible `n` form a finite or ultimately
periodic residue set.

## 2. Certified family

Fix distinct binary letters `a,b`. Let

    p_n = delta(start,a^n)
    N   = { n>=0 : p_n is defined and delta(p_n,b) is defined }.

Because the state set is finite, `N` is finite or ultimately periodic. For each
leading state `p` occurring for some `n in N`, put `q_p=delta(p,b)`.

Let `Good` be the finite set of controls `q` for which every positive trailing
power is defined and has the required terminal suffix:

    for every m>=1, delta(q,a^m b a)=final.

This is decidable from the finite positive `a`-orbit of `q`.

For each branch `p`, define the regular middle language

    M_p = { u : delta(q_p,u) in Good }.

The verifier checks exactly, by DFA x epsilon-NFA symmetric-difference
emptiness, that the boundary-safe candidate language is

    L = { a^n b u a^m b a : n in N, m>=1, u in M_{p_n} }.

It also checks that every nonempty `u in M_p` begins with `a`. Empty `u` is
allowed. This last condition is exactly what the cut proof needs after the
first `b`.

## 3. Three exhaustive arithmetic cases

Fix a candidate

    w = a^n b u a^m b a,

with middle endpoint `q=delta(q_{p_n},u) in Good`.

### Case n < m

Put `d=m-n>=1` and `r=delta(q,a^d)`. Since `q in Good`, `r` lies in its finite
positive `a`-orbit. The suffix at `r` is

    a^n b a.

The suffix at the start begins

    a^n b a

because `u` is empty or begins with `a`. Thus the target suffix is a prefix of
the source suffix. Requiring flag `(start,r)` certifies a violation.

### Case n = m

The suffix at `q` is `a^n b a`, and the start suffix has the same prefix for
the same middle-first-letter reason. Requiring `(start,q)` certifies a
violation.

### Case n > m

Put `d=n-m>=1` and `s=delta(start,a^d)`. This state exists because the accepted
candidate has a defined `a^n` prefix. The suffix at `s` begins

    a^m b a,

while the suffix at `q` is exactly `a^m b a`. Requiring `(s,q)` certifies a
violation.

These cases are exhaustive and use only finite sets of controls:

- all defined positive leading-prefix states `s`;
- all branch-specific middle effects `q`;
- all positive trailing-orbit states `r`.

The verifier checks every required pair is an actual flag. Therefore every
candidate has an explicit violating cut, proving NO for the whole infinite
language.

## 4. Strict extension over the single-anchor rule

A parity-split eight-state fixture accepts exactly

    0* 1 0+ 1 0

but the first `1` reaches one of two different anchors depending on parity of
the leading zero run. The old automatic three-way certificate is inconclusive;
the orbit-split verifier returns `VERIFIED_NO`.

A second fixture exposes a genuine residue parameter:

    N = { 2t : t>=0 }.

The leading zero orbit alternates between two controls but the first `1` exists
only on the even-residue control. The candidate language is exactly

    0^(2t) 1 0+ 1 0.

Again the old single-anchor/all-leading-powers synthesis is inconclusive, while
the new verifier proves NO all-length.

The important point is not these small fixtures. The certificate now contains a
real finite Presburger component: one parameter may range over an ultimately
periodic subset of the naturals, while its regular middle language and required
cut controls vary by residue/orbit state.

## 5. What this still does not cover

The trailing length `m` is still universally positive rather than restricted by
its own residue class, and the proof uses only the order partition
`n<m`, `n=m`, `n>m`. More general NO languages may require:

- independent ultimately periodic domains for several unary parameters;
- affine relations such as `2n<m+3` rather than plain order;
- several regular middle segments;
- cut positions that are affine functions of multiple parameters;
- a finite union of such symbolic cells.

The next natural theorem is therefore a finite Presburger cut-selector cover:
each cell supplies a semilinear parameter domain, finite-state regular segment
effects, affine source/target offsets, and a flag/equality proof checked by
finite automata plus Presburger arithmetic. Completeness is not established.

## 6. Reproduction

Run

    python3 experiments/check_orbit_split_cut_certificate.py

The verifier itself checks candidate-language equality and all orbit premises
exactly. Bounded word enumeration in the regression is differential evidence,
not the all-length proof. The checker includes the two-anchor parity fixture,
the even-residue fixture, required-flag mutations, and a positive control that
must remain inconclusive.

[Implementation](../experiments/orbit_split_cut_certificate.py) ·
[checker](../experiments/check_orbit_split_cut_certificate.py) ·
[result](../results/orbit-split-cut-certificate.json).

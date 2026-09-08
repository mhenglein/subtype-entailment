# Two-parameter residue three-way cut certificates

Date: 2026-09-08. Continues `2026-09-08-orbit-split-cut-certificates.md`.

**Status: written proof + exact finite verifier + recorded CI regression;
independent mathematical review pending; not Lean-checked. Unrestricted Problem
1.7 remains open.**

## 1. Statement

Fix distinct binary letters `a,b`, one terminal final `f`, no Bad states and
boundary-normalized flags. The verifier recognizes candidate languages with
factorizations

    a^n b u a^m b a,

where both numeric parameters have finite-state residue restrictions.

The leading domain is

    N = { n>=0 : delta(start,a^n b) is defined }.

For each leading orbit state `p_n`, its `b` edge chooses a branch-specific
middle anchor. The middle endpoint `q` may vary over a regular language.
The trailing domain from that endpoint is

    M_q = { m>=1 : delta(q,a^m b a)=f }.

Since powers of one transition function eventually cycle, `N` and every
`M_q` are finite or ultimately periodic. The verifier does not approximate
these sets by a numeric cutoff: it tracks the finite control orbit exactly.

It then proves NO by the same exhaustive arithmetic partition:

* `n<m`: with `d=m-n`, compare the start to `delta(q,a^d)`;
* `n=m`: compare the start to `q`;
* `n>m`: with `d=n-m`, compare `delta(start,a^d)` to `q`.

Every possible finite control pair induced by these formulas is required to be
an actual flag. Candidate-language equality to the symbolic family is checked
exactly by product reachability against a finite epsilon-NFA. Consequently
`VERIFIED_NO` is an all-length theorem for the supplied instance.

## 2. Why trailing residues are sound

The previous orbit-split rule required

    delta(q,a^m b a)=f  for every m>=1.

That is stronger than the cut proof needs. In a candidate word only the actual
accepted `m` matters. If the `a`-orbit from `q` alternates controls and only some
of them possess the terminating `b a` path, the admissible `m` are periodic.

For `n<m`, the comparison state `delta(q,a^(m-n))` need not itself be a
terminal-residue state; it only has to exist on the positive `a`-orbit, which it
does because the accepted trailing run contains at least `m` copies. Therefore
the finite required-flag set uses the whole positive orbit for the `n<m` case,
while candidate-language acceptance restricts the final exponent to the true
terminal residue set. The `n=m` and `n>m` cases are unchanged.

## 3. Strict fixture

The six-state regression accepts exactly

    0^n 1 0^(2t+1) 1 0,
    n,t>=0.

The trailing zero count is odd. The old three-way rule is inconclusive because
not every positive trailing exponent reaches the final. The one-residue orbit
split is likewise inconclusive. The two-residue verifier returns
`VERIFIED_NO`.

The all-length proof uses the three cases above. Bounded enumeration through
length 14 checks the independent language formula and direct witness predicate
only as differential evidence. Removing any required flag makes this exact
certificate unavailable.

## 4. Exact-small-census diagnostic

For transparency, the checker also compares the symbolic recognizers against
the repository's independent exact <=3-state theorem on all 1,034 normalized
terminal instances. There are 464 exact NO instances, but none matches the
three-way/orbit/bi-residue shapes. This is useful negative evidence: the new
certificate is a structural rule for larger recurrent languages, not a claim
that one pattern explains the small census.

## 5. Toward a Presburger cut-selector calculus

The residue rule exposes the abstraction more clearly. A complete symbolic NO
certificate need not enumerate words. It may instead provide finitely many
cells containing:

1. semilinear domains for repetition parameters;
2. regular finite-state effects for unconstrained middle segments;
3. affine formulas for source and target cuts;
4. a finite proof that the selected controls are flagged; and
5. an exact coverage proof that the cells cover the entire candidate language.

Here the cells are only `n<m`, `n=m`, `n>m`, and the affine offsets have
coefficients in {-1,0,1}. Nothing yet proves that arbitrary terminal instances
admit a finite cover of this form. The regular-decoration barrier makes this
symbolic-cover route materially different from another finite-state marking
scheme.

## 6. Reproduction

Run

    python3 experiments/check_bi_residue_cut_certificate.py

[Verifier](../experiments/bi_residue_cut_certificate.py) ·
[checker](../experiments/check_bi_residue_cut_certificate.py) ·
[result](../results/bi-residue-cut-certificate.json).

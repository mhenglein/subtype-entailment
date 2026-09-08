# Finite arithmetic cut selectors

Date: 2026-09-08. Workstreams: A012/A017; issue #15.

**Status: exact finite verifiers + written all-length proofs + reproducible
regressions; independent mathematical review pending; not Lean-checked.
Unrestricted Problem 1.7 remains open.**

## What changed

The regular-decoration barrier rules out a broad class of complete methods that
preserve every candidate and only add finite-state marker memory before applying
a bounded semantic-tail test. The next installed route instead partitions an
infinite candidate language symbolically and selects an actual violating cut in
each arithmetic cell.

The first rule, `three_way_cut_certificate.py`, handles

    a^n b M a^m b a

by the exhaustive cells `n<m`, `n=m`, `n>m`, with an arbitrary regular middle
language M. Automatic synthesis was repaired on 2026-09-08: a maximal set of
middle endpoints can create unnecessary decompositions and flag obligations, so
the synthesizer now enumerates finite endpoint subsets and lets exact candidate-
language equality plus the theorem verifier select a genuine cover.

The orbit/residue extension removes the single-anchor/all-leading-powers
restriction. The leading `a`-orbit may choose different `b` anchors, and `b` may
exist only on selected orbit states. Hence the leading parameter ranges over a
finite or ultimately periodic set.

The bi-residue extension also lets the trailing parameter depend on its own
finite orbit:

    M_q = {m>=1 : delta(q,a^m b a)=final}.

Both numeric domains are therefore finite/ultimately periodic, middle effects
remain regular, and the same three affine cut formulas provide the all-length
NO proof.

## Exact evidence

`check_orbit_split_cut_certificate.py` records two strict examples:

- a parity-split language where two leading orbit states use different anchors;
- an even-only leading parameter `n in 2N`.

The prior automatic three-way rule is inconclusive on both and the orbit rule
returns `VERIFIED_NO`.

`check_bi_residue_cut_certificate.py` adds a language

    0^n 1 0^(2t+1) 1 0,

where the trailing exponent is genuinely odd-only. Both prior rules are
inconclusive and the bi-residue rule returns `VERIFIED_NO`.

For transparency, the bi-residue checker compares all three symbolic recognizers
against the independent exact <=3-state theorem over all 1,034 normalized
instances. There are 464 exact NO instances and none matches these three-way
shapes. This is negative coverage evidence, not a theorem failure: the rules
capture larger recurrent arithmetic families rather than the small census.

[Orbit/residue proof](../notes/2026-09-08-orbit-split-cut-certificates.md) ·
[orbit result](../results/orbit-split-cut-certificate.json) ·
[bi-residue proof](../notes/2026-09-08-bi-residue-cut-certificates.md) ·
[bi-residue result](../results/bi-residue-cut-certificate.json).

## Candidate general calculus

A finite Presburger cut-selector certificate would consist of finitely many
cells. Each cell should contain:

1. a semilinear domain for repetition/length parameters;
2. regular finite-state constraints for unconstrained word segments;
3. affine formulas selecting source and target cut positions;
4. a finite proof that those cuts carry a permitted flag and that the selected
   terminal suffix equals the corresponding source prefix; and
5. an exact regular/arithmetic coverage proof for the entire candidate language.

The installed residue rules realize this schema with two unary parameters,
ultimately-periodic domains, one regular middle, and affine coefficients in
`{-1,0,1}`. No completeness theorem says every terminal NO instance admits such
a finite cover.

## Backreference/literature boundary

The non-overlap component of terminal badness has the one-use backreference
shape `A(B)_x C x` with the copied occurrence terminal; overlap has a bounded
periodic form by terminal nonmerging. Kumabe--Uezato (ICALP 2026) normalize
arbitrary 1-use REWBs to finite unions of `A(B)_x C x D` branches and give
near-linear membership, but that is a per-word matching result, not the
regular-language containment/universality problem needed here.

Thompson--Freydenberger's FC[REG]-CQ universality construction is genuinely
undecidable, but its invalid-computation patterns use arbitrary trailing
contexts, internal repeated variables, and multiple regularly typed unary
variables. Those gadgets do not directly have the terminal-copy shape. In
particular, a local computation error in the middle of a history is not
automatically expressible by a copy whose second occurrence extends to the end
of the entire candidate. Therefore that theorem is an adversarial warning, not
a reduction to Subtail.

No reviewed source located in this continuation directly decides or proves
undecidable the special problem

    regular R subseteq finite union of state-constrained terminal one-copy
    languages plus bounded-overlap languages.

That exact containment problem remains the cleanest language-theoretic frontier.

## Next discriminating tasks

1. Generalize cut cells from unary powers to powers of a fixed nonempty word and
   then to finite transition-monoid fibres, while retaining exact coverage.
2. Determine whether a finite union of semilinear cut-selector cells is complete
   for the six-state regular-decoration barrier and for the counting/synchrony
   families already in the repository.
3. Audit whether the ICALP 2026 factorization-forest/transition-monoid machinery
   for one-use matching can be lifted from one input word to a regular candidate
   automaton. Such a lift would be substantially closer to a total algorithm.
4. On the adversarial side, an undecidability reduction must solve the terminal
   anchoring problem explicitly; citing general FC[REG] universality is not
   sufficient.

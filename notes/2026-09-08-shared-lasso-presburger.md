# Shared-lasso schemas remain Presburger-decidable

Date: 2026-09-08. Workstream: A016/A017. Consolidated claim: C063.

**Status: written proof; independent review pending; not Lean-checked. No unrestricted decision is claimed.**

## 1. Shared-lasso skeletons

Fix a finite annotated DFA instance `I` and nonnegative integer parameters `n_1,...,n_r`. A shared-lasso skeleton is

    s_0 u_1^(n_g(1)) s_1 ... u_d^(n_g(d)) s_d,

where each `s_i` and each nonempty `u_i` is a fixed word and `g(i)` selects one of the shared parameters. Different repeated blocks may therefore use the same exponent.

### Theorem A — witness vectors are Presburger-definable

The set of parameter vectors whose instantiated word is a witness of `I` is effectively Presburger-definable. Hence witness existence in any supplied shared-lasso skeleton is decidable.

A016 already supplies an exact Presburger translation for a fixed skeleton with a fresh exponent `m_i` per repeated block. Its clauses use only linear boundary expressions, powers of fixed finite actions represented by finite preperiod/congruence cases, fixed-modulus position tests, and linear interval guards. To share an exponent, either substitute `m_i := n_g(i)` or retain the fresh variables and conjoin `m_i=m_j` whenever `g(i)=g(j)`. No multiplication of variables is introduced. Presburger arithmetic is closed under conjunction and projection, proving the theorem. Fixed affine aliases are handled similarly with nonnegativity guards.

## 2. Boundary-safe minimum violations

The minimum-violation statement requires a boundary-safety hypothesis. This is essential and was missing from the first draft.

Call an instantiated candidate **boundary-safe** when all non-proper failure modes have already been excluded: the run is defined, no Bad state is visited, the endpoint is accepting, no visited state has a diagonal flag, and no visited source has a flag into the final/empty-suffix state. For a boundary-safe non-witness `w`, define

    mu(w) = min { |w|-j : i<j<|w| is a forbidden proper suffix agreement }.

This set is nonempty exactly because the word is boundary-safe but is not a witness.

### Theorem B — minimum-violation growth is decidable inside one boundary-safe schema

For a supplied shared-lasso skeleton, the relation

    P(n_1,...,n_r,H)
      := the instantiated word is boundary-safe,
         is not a witness, and mu(w) > H

is effectively Presburger-definable. Consequently

    U = { H : exists n_1,...,n_r . P(n_1,...,n_r,H) }

is an effectively semilinear subset of the naturals. It is decidable whether `U` is empty, finite nonempty, or unbounded; in the finite nonempty case its maximum is computable.

### Proof

For boundary-safe words, the repository predicate `Necessary(H,0)` says precisely that no proper forbidden comparison of target length at most `H` occurs. The A016 positional mismatch formula remains Presburger after adding the linear guard `N-j <= H`. Hence `Necessary(H,0)` is Presburger-definable jointly in the shared exponents and `H`. Theorem A makes full witnesshood Presburger-definable as well. On the boundary-safe domain,

    Necessary(H,0) and not Witness

is exactly `mu(w)>H`. Conjoin the Presburger boundary-safety clauses and project away the exponent variables. Closure of Presburger arithmetic under projection gives the semilinear set `U`, whose emptiness, boundedness, and finite maximum are effective.

Do **not** use this equivalence on merely admissible words. For example, a word can have a proper minimum violation larger than `H` while a diagonal or empty-suffix flag already makes `Necessary(H,0)` false. Boundary normalization is therefore part of the theorem, not a cosmetic preprocessing step.

Also note the quantifier bookkeeping: for a fixed word with `mu(w)=m`, the permitted nonnegative thresholds are `H<m`; `max(U)` is a threshold statistic, not automatically the maximum value of `mu` itself. If `U` is empty it has no maximum.

## 3. Current benchmark separation

The seven-state constant-short-violation family has boundary-safe bad candidates with `mu=1` even though another last-aligned comparison can grow without bound. Its corresponding threshold set contains no `H>=1`.

The five-state necessary-budget counterexample contains the shared-exponent subfamily

    1^n 0 1^n 10,

whose unique proper violation has target length `n+1`. Its threshold set is unbounded. Thus shared-exponent Presburger analysis can distinguish constant-short and escaping-minimum behavior inside a supplied schema while coordinating all comparisons in the same instantiated word.

## 4. Remaining gap

A finite union of supplied shared-lasso schemas is decidable by the preceding translation. The unresolved issue is **coverage** for arbitrary nonflat productive components: find an effective finite existence-preserving reduction to such schemas, or another complete normalization. Generic shared-template iteration cannot simply be treated as a decidable black box.

A relevant technique source is V. Havlena, M. Hečko, L. Holík, O. Lengál, *Negated String Containment Is Decidable*, MFCS 2025, DOI 10.4230/LIPIcs.MFCS.2025.56. Their one-negated-containment reduction does not directly solve the synchronized family of state-coloured comparisons here, but its nonflat-to-flat reduction remains a useful source of ideas.

# Shared-lasso schemas remain Presburger-decidable

Date: 2026-09-08. Workstream: A016/A017. Base main: `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status: written proof. Independent review pending; not Lean-checked. No unrestricted decision is claimed.** This note connects the fixed-skeleton arithmetic of A016 with the shared-word/recurrent-target work of A017.

## 1. Exact statement

Fix a finite annotated DFA instance `I`. Fix finitely many nonnegative integer parameters

    n_1, ..., n_r.

A **shared-lasso skeleton** is a word expression

    s_0 u_1^(n_g(1)) s_1 ... u_d^(n_g(d)) s_d,

where every `s_i` and every nonempty `u_i` is a fixed word, and each map value `g(i)` lies in `{1,...,r}`. Thus the same exponent variable may occur in several separated repeated blocks. The repeated blocks themselves may be different fixed words; aliasing constrains only their repetition counts.

### Theorem A — witness vectors are Presburger-definable

The set of parameter vectors `(n_1,...,n_r)` whose instantiated word is a witness of `I` is effectively Presburger-definable. Hence witness existence in a supplied shared-lasso skeleton is decidable.

### Theorem B — global-minimum violation growth is decidable inside one schema

For an admissible non-witness `w`, let

    mu(w) = min { |w|-j : i<j<|w| is a forbidden suffix agreement }.

For a shared-lasso skeleton, the relation

    P(n_1,...,n_r,H)
      := instantiated word is a non-witness and mu(w) > H

is effectively Presburger-definable. Consequently the set

    U = { H : there exists a parameter vector with P(n_1,...,n_r,H) }

is Presburger-definable. It is therefore decidable whether `U` is bounded or unbounded; if bounded, its exact maximum is computable.

This is an exact all-parameter result for the supplied schema. It is not a finite cover theorem for arbitrary terminal automata.

## 2. Proof of Theorem A

A016 already gives an exact Presburger translation for a fixed skeleton

    s_0 u_1^m_1 s_1 ... u_d^m_d s_d

with a fresh nonnegative exponent `m_i` for every repeated block. Inspecting that construction shows that each exponent occurs only in:

1. linear block-boundary expressions such as `o_{i+1}=o_i+|u_i|m_i`;
2. powers of a fixed finite transition action, whose state after `m_i` copies is expressed by finitely many preperiod cases and a congruence modulo a fixed period;
3. fixed-modulus arithmetic locating a position inside a repeated block;
4. interval guards and the outer quantified position variables used by the exact mismatch formula.

There is no product of two integer variables. The proof of exactness does not require the exponent variables for distinct blocks to be distinct.

Replace every fresh `m_i` by the shared parameter `n_g(i)`. Equivalently, retain the fresh variables and conjoin the linear equalities

    m_i = m_j whenever g(i)=g(j).

Presburger arithmetic is closed under conjunction and existential quantification, so the resulting formula is Presburger. Its semantics is exactly the shared-lasso language because equalities force every aliased block to use one common repetition count. This proves Theorem A.

The same argument allows affine aliases such as `m_j=n_a+c` for fixed integer constants `c`, provided nonnegativity is guarded. No variable multiplication is introduced.

## 3. Proof of Theorem B

For a fixed nonnegative `H`, the repository's exact `Necessary(H,0)` predicate says that the word is admissible and has no forbidden suffix agreement whose target suffix length is at most `H`. In positional form, replace the full witness obligation

    flagged(i,j) => mismatch(i,j)

by

    flagged(i,j) and N-j <= H => mismatch(i,j).

The A016 mismatch elimination is unchanged: within two fixed blocks, letters depend only on positions modulo fixed word lengths; existence of a mismatch is a finite disjunction over fixed residue classes. The additional guard `N-j <= H` is linear. Therefore `Necessary(H,0)` is Presburger-definable jointly in the shared exponents and `H`.

The full witness predicate is Presburger-definable by Theorem A. Hence

    Necessary(H,0) and not Witness

is Presburger-definable and, for boundary-safe words, is exactly `mu(w)>H` with `w` still a non-witness. This gives `P`.

Existentially project the exponent variables. Presburger arithmetic remains closed under projection, giving a one-dimensional semilinear set `U` of admissible values of `H`. Boundedness of a semilinear subset of the naturals is decidable, and a bounded set has an effectively computable maximum. This proves Theorem B.

Boundary failures (Bad, undefined, nonfinal, diagonal, or empty-suffix flags) may either be normalized away first, as in the terminal work, or retained as the existing Presburger admissibility clauses. They do not affect the argument.

## 4. It separates the two current NO benchmarks

The September 7 last-flag note deliberately separated two phenomena.

### Seven-state constant-short-violation family

Its accepted language is

    1^n 00 1^m 00,    n,m>=1,

and every candidate has a one-letter violation from the second flag. Therefore `mu(w)=1` for every candidate, although another last-aligned comparison can have unbounded length. In the shared-lasso schema with independent `n,m`, the set `U` from Theorem B is bounded (indeed no `H>=1` belongs to it).

### Five-state all-budget counterexample

The earlier NO family contains the subfamily

    1^n 0 1^(n+1) 0.

Write this as the shared-exponent skeleton

    1^n 0 1^n 10.

The recorded exact analysis gives one violation whose target length is `n+1` and gap is `n+2`, with no smaller violation. Hence `mu(w)=n+1`; the corresponding `U` is unbounded.

Thus shared-exponent Presburger analysis distinguishes the examples for the right reason: it coordinates different comparisons in the SAME instantiated word, instead of inspecting one marked last flag in isolation.

## 5. Why this still does not close the problem

The missing theorem has moved again but has not disappeared.

A finite union of supplied shared-lasso schemas is completely decidable by Theorems A and B. Flat terminal graphs already admit such a finite complete cover. The recurrent residual examples also have tiny shared-parameter descriptions once a particular schema is known.

The obstruction is **coverage** for a general nonflat productive component. A regular path language need not be a finite union of bounded-depth lasso expressions with a fixed finite set of exponent aliases. Non-flat regular languages can contain arbitrarily interleaved choices of cycles. Generic iteration of shared-word templates is too expressive: the prior PCP observation prevents treating unrestricted template iteration as a decidable black box.

So the next constructive target is precise:

> Produce an effective finite cover of every terminal candidate language by shared-lasso schemas sufficient for witness existence, or prove a normalization that replaces an arbitrary successful word by one in such a finite cover.

A weaker but still useful target is a finite cover only for words with `mu(w)` above a supplied threshold; Theorem B would then decide whether global minimum violations can escape every finite bound.

## 6. Relation to recent not-contains decidability

Havlena, Hečko, Holík and Lengál, *Negated String Containment Is Decidable* (MFCS 2025), prove decidability of one `¬Contains(N,H)` constraint where `N,H` are string terms and variables have arbitrary regular constraints, and extend this to chain-free word equations with one such predicate.

That theorem is relevant because its proof handles non-flat regular variable languages by a finite reduction to flat languages using word-combinatorial structure. It cannot simply be cited as a solution here. A terminal witness forbids **all** state-coloured suffix agreements arising from all internal cuts of the same candidate, not one supplied needle/haystack assignment, and the paper explicitly leaves multiple `¬Contains` constraints as future work.

Nevertheless its flat/non-flat reduction is now a high-value source of techniques for the remaining coverage theorem. In particular, the shared-lasso theorem above means that any sound reduction of our non-flat fibres to finitely many flat/shared-lasso cases would plug directly into an existing exact arithmetic backend.

Primary reference: V. Havlena, M. Hečko, L. Holík, O. Lengál, *Negated String Containment Is Decidable*, MFCS 2025, DOI 10.4230/LIPIcs.MFCS.2025.56.

## 7. Handoff

Do not search for another numerical bound before addressing schema coverage. The most discriminating next attempt is to adapt the MFCS 2025 flat/non-flat reduction to one state-coloured terminal-copy obligation and then test whether finitely many such reductions can be synchronized without losing the common candidate word. A counterexample to that synchronization would be equally valuable.

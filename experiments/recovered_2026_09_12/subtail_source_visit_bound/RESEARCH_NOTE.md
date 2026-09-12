# Source-visit lower bounds for Subtail's modular synchronization family

Date: 2026-09-10. Repository snapshot: `f85ba3af769041349979e6130f1e2bc109b07c91`.
Relevant workstreams: A008/A009/A017; existing construction C046; question Q004.

**Result status: written derivation and executed finite regression checks. No independent mathematical review or Lean verification was performed. This is NOT a solution of unrestricted subtype entailment, a general BorderAvoid decider, or a refutation of Q004.**

The modular automata and their exact witness languages are existing repository work [1,2]. This note extracts their exact flagged-source visit counts, supplies certificates that every flag is genuinely live for a coprime specialization, and derives a prime-parameter lower bound. It makes no priority claim for the construction or these consequences. No repository claim IDs have been allocated and no remote files have been changed.

## 1. Exact target and the attempted end-to-end route

The original task concerns bottom and covariant binary product over arbitrary, possibly infinite trees, not just finite trees [3]. The relevant terminal BorderAvoid formulation has a partial binary DFA

\[
I=(Q,\{0,1\},\delta,q_0,F,\mathrm{Bad},G),
\]

where every final state has no outgoing transition. A word `w` of length `n` is admissible if its run `c(0),...,c(n)` is defined, avoids Bad at every position, and ends in F. It is a witness when

\[
\forall\,0\le i\le j\le n,\qquad
w[j:]\preceq w[i:]\ \Longrightarrow\ (c(i),c(j))\notin G.
\]

The prefix comparison includes the diagonal `i=j` and the empty suffix `j=n`. Define

\[
S(I)=\{p:\exists t\;(p,t)\in G\},\qquad
\nu_I(w)=|\{i:0\le i\le n,\ c(i)\in S(I)\}|.
\]

Thus visits count positions, not merely distinct source-state labels. For a positive instance put

\[
\nu_{\min}(I)=\min\{\nu_I(w):w\text{ is a witness}\}.
\]

C068 gives an exact existential word-equation formulation for any supplied finite source-visit sequence, with regular constraints and shared suffix variables [4]. A computable bound on the length of such sequences would make that route a general decision procedure. The attempted closing claim would be a total computable function R satisfying

\[
\forall I\text{ with }k\text{ states},\quad
\mathrm{Witness}(I)\ne\varnothing\Longrightarrow\nu_{\min}(I)\le R(k).
\]

That is Q004 [5]. The calculations below rule out polynomial choices for R. They do not rule out larger computable bounds and do not supply an upper bound. The unrestricted termination/coverage implication remains unproved in this attempt.

The imported decision theorem underlying the supplied-sequence route is Theorem 4 of Diekert, Gutierrez and Hagenah: existential word equations with finite-automaton constraints in free monoids with involution are decidable in PSPACE [6]. The repository explicitly restricts variables to binary words and does not invoke free-group cancellation. Deciding each supplied sequence does not decide the unbounded set of sequences.

## 2. The existing automaton, defined completely

Choose `r >= 2` positive integer periods `p_1,...,p_r`. For block i introduce an entry state `e_i` and cycle states `q_(i,1),...,q_(i,p_i)`. Introduce one additional final state f. All these states are distinct. The initial state is `e_1`, the final set is `{f}`, and Bad is empty.

The transitions are

\[
\delta(e_i,1)=q_{i,1},\qquad
\delta(q_{i,d},1)=q_{i,d+1}\quad(1\le d<p_i),\qquad
\delta(q_{i,p_i},1)=q_{i,1}.
\]

On letter 0, the only transitions are from `q_(i,p_i)` to `e_(i+1)` for `i<r`, and from `q_(r,p_r)` to f. All other transitions, including both transitions from f, are undefined.

For each `i<r`, put precisely the following flags in G:

\[
(e_i,q_{r,d})\quad(1\le d\le p_r),\qquad
(q_{i,d},e_r)\quad(1\le d\le p_i).
\]

There are

\[
k=1+r+\sum_{i=1}^r p_i
\]

states. Every state is reachable from the start and can reach f. Each productive cyclic component is just one unary cycle, so the graph is flat. The language of admissible words is exactly

\[
1^{n_1}0\,1^{n_2}0\cdots1^{n_r}0,
\qquad n_i>0,\quad p_i\mid n_i.
\]

No hidden side conditions, additional letters, epsilon transitions, or nonterminal final states are used.

## 3. Exact witness language and source-visit minimum

**Proposition.** Let `L = lcm(p_1,...,p_r)`. Then

\[
\mathrm{Witness}(I)=\{(1^N0)^r:N\in L\mathbb N_{>0}\},
\]

and

\[
\boxed{\nu_{\min}(I)=(r-1)(L+1).}
\]

The shortest witness has length `r(L+1)`.

**Proof of the language characterization (rechecking existing C046).** Consider an admissible word with block counts `n_1,...,n_r` and fix `i<r`.

If `n_i<n_r`, take the source at entry `e_i`. In the last block, after `n_r-n_i` ones, the remaining word is exactly `1^(n_i)0`. This target lies in the last cycle, and its suffix matches the beginning of the source suffix. The relevant flag `(e_i,q_(r,d))` is therefore violated.

If `n_i>n_r`, take the source after `n_i-n_r` ones in block i and the target at `e_r`. The target suffix `1^(n_r)0` matches the beginning of the source suffix. This violates a flag `(q_(i,d),e_r)`.

Consequently a witness requires `n_i=n_r` for each earlier block. The common positive count N must be divisible by every period.

Conversely, suppose all counts equal N. At any last-cycle target there are fewer than N ones remaining before its closing 0, so its suffix cannot match the beginning of an earlier entry suffix, which has N initial ones. At any earlier-cycle source there are fewer than N ones before its next 0, so the suffix from `e_r`, which starts with N ones, cannot match there. These are all the flags. No diagonal or final-column flag exists, and Bad is empty. Hence the word is a witness.

**Proof of the source count.** The source-state set is exactly

\[
S(I)=\bigcup_{i<r}\bigl(\{e_i\}\cup\{q_{i,d}:1\le d\le p_i\}\bigr).
\]

For a witness `(1^N0)^r`, each earlier block contributes its one entry position and N cycle positions. Its closing 0 leads to the next block's entry, which is counted with that next block if it is a source. The last entry, the last cycle, and f are not sources. Thus

\[
\nu_I((1^N0)^r)=(r-1)(N+1).
\]

The smallest permitted N is L, and increasing N increases both this count and the word length. This proves both minima over *all* witness lengths. QED.

On this family the minimum source count happens to equal the sufficient budget computed in C046. No equality of these two quantities is asserted for general instances.

## 4. Dead flags do not explain the lower bound

Call a flag genuinely live if there exists an admissible word with an actual forbidden suffix-prefix agreement using that exact ordered pair. This is stronger than merely requiring the source and target to occur in order on an accepted path.

**Proposition.** If `gcd(p_i,p_r)=1` for every `i<r`, every flag in the construction is genuinely live.

**Proof.** Fix `i<r`.

For `(e_i,q_(r,d))`, where `1<=d<=p_r`, coprimality permits a positive multiple a of `p_i` such that `a+d` is divisible by `p_r`. Take `n_i=a`, `n_r=a+d`, and any allowed positive counts in the other blocks. The source is at `e_i`; the target is after d ones in the last block, at the specified cycle state. The target suffix is exactly `1^a0`, matching the beginning of the source suffix.

For `(q_(i,d),e_r)`, where `1<=d<=p_i`, choose a positive multiple a of `p_r` such that `a+d` is divisible by `p_i`. Take `n_i=a+d`, `n_r=a`, and allowed counts elsewhere. The source after d ones in block i is the specified state. The suffix from `e_r` is `1^a0`, which matches there.

These choices exist because multiplication by a number coprime to a modulus permutes its residues. Taking the multiplier in `1,...,modulus` ensures positivity, including the zero-residue case. All constructed words are admissible. Each displayed agreement certifies its exact flag; other simultaneous violations are irrelevant. QED.

Thus removing dead states or genuinely dead flags does not remove this obstruction. In particular the statement applies when the periods are distinct primes.

## 5. A sharper asymptotic from prime periods

Take all primes at most x as periods, with x tending to infinity and at least two primes included. Write `r=pi(x)` and `theta(x)=sum_(p<=x) log p`, using natural logarithms. Since the periods are distinct primes,

\[
L_x=\prod_{p\le x}p,\qquad \log L_x=\vartheta(x).
\]

The prime-number estimates used here are only `theta(x) ~ x` and `pi(x) ~ x/log x`. Both follow from the bounds in Dusart [7], Theorem 5.2 and Section 6.2; no Riemann-hypothesis assumption is used.

Partial summation gives

\[
\sum_{p\le x}p=x\pi(x)-\int_2^x\pi(t)\,dt
\sim\frac{x^2}{2\log x}.
\]

For clarity, the integral is asymptotic to `x^2/(2 log x)`, while `x*pi(x)` is asymptotic to `x^2/log x`. Subtracting leaves the stated leading term. The additive entry-state cost `pi(x)+1` is lower order. Therefore

\[
k_x=1+\pi(x)+\sum_{p\le x}p\sim\frac{x^2}{2\log x},\qquad
\sqrt{k_x\log k_x}\sim x.
\]

Meanwhile

\[
\log\nu_{\min}(I_x)
=\log(\pi(x)-1)+\log(L_x+1)\sim x.
\]

Consequently this explicit family satisfies

\[
\boxed{\lim_{x\to\infty}
\frac{\log\nu_{\min}(I_x)}{\sqrt{k_x\log k_x}}=1.}
\]

Equivalently, along the family,

\[
\nu_{\min}(I_x)=\exp\!\bigl((1+o(1))\sqrt{k_x\log k_x}\bigr).
\]

Any universal R in Q004 must dominate these values at these state counts. In particular, no polynomial in k can serve as R. This is an asymptotic for the explicit family, **not an upper bound for arbitrary instances**, and no optimality among all constructions is claimed.

An elementary weaker version needs no prime-number theorem: use periods `1,...,m` and the repository's divisibility bound `lcm(1,...,m) >= 2^m/(m+1)` [1]. The same source-count formula then gives `nu_min >= 2^(m-1)` for `m>=3`, with `k=(m+1)(m+2)/2`. This alone already rules out polynomial source-visit bounds.

## 6. Concrete values

All rows are exact arithmetic consequences of the all-length formula. Large words were not enumerated or materialized merely to compute these values.

| Periods | States k | L | Minimum source visits | Shortest witness length |
|---|---:|---:|---:|---:|
| 2, 3 | 8 | 6 | 7 | 14 |
| 2, 3, 5 | 14 | 30 | 62 | 93 |
| 2, 3, 5, 7 | 22 | 210 | 633 | 844 |
| 2, 3, 5, 7, 11 | 34 | 2,310 | 9,244 | 11,555 |
| 2, 3, 5, 7, 11, 13 | 48 | 30,030 | 150,155 | 180,186 |
| 2, 3, 5, 7, 11, 13, 17 | 66 | 510,510 | 3,063,066 | 3,573,577 |
| 2, 3, 5, 7, 11, 13, 17, 19 | 86 | 9,699,690 | 67,897,837 | 77,597,528 |

For example, the 14-state instance has seven distinct source states, but every witness visits source states at least 62 times. Counting distinct labels as visits would therefore give an incorrect bound.

## 7. Executed checks and their limits

Reproduce with Python 3.9 or newer and no third-party packages:

```sh
python3 source_visit_bound.py --self-test --output replay.json
```

The local run used Python 3.13.5. `results.json` stores the complete deterministic output, including each live-flag certificate as block counts and exact cuts. `run.log` is the compact console output. The script refuses to run its tests with assertions disabled by `-O`.

The checks compare a direct suffix-prefix cut predicate, a separately implemented reversed-prefix-border predicate, and an arithmetic language specification. They include:

- 40,955 raw binary-word comparisons, over the ranges recorded in the JSON;
- all 3,468 accepted paths of the 14-state instance through length 93, and all eight accepted paths of the eight-state instance through length 14;
- 2,384 exponent-vector comparisons over multiple period tuples, including noncoprime and repeated periods;
- direct checks of all 1,161 live-flag certificates for the first 2 through 10 prime periods;
- three materialized least witnesses, nine empty/diagonal/Bad/multiple-final/undefined-path boundary cases, the printed eight-state repository fixture, and the existing two-source loop-deletion counterexample.

The two-source regression from C067/C068 uses

```text
start 0; final 4; flags {(0,1),(2,0)}; Bad empty
0: (1,2)
1: (4,1)
2: (3,2)
3: (1,0)
4: (-1,-1)
```

Both predicates accept `110010` as a witness and reject the still-admissible `10010` after a loop deletion. The latter has a new violation at cuts `(0,3)` with flag `(0,1)`. This demonstrates why later-source compression cannot simply ignore earlier-source obligations. It does not refute every possible normalization.

The finite searches prove shortestness for the two completely searched length ranges. The global source minima and asymptotic conclusions come from the written proofs, not from extrapolating these tests. Shared implementation of the underlying DFA run is disclosed; the two word predicates are not separate proof-assistant verifications. No full repository CI, Lean build, independent reviewer, or new subtype-reduction audit is claimed.

## 8. What remains unresolved

The modular family is itself decided by an LCM calculation and lies within the repository's already-decided flat-terminal class. Large witnesses therefore do not establish undecidability or even a lower bound on the complexity of a symbolic existence decision.

Q004 asks for a computable bound, not a polynomial one. This investigation does not prove or refute that statement. The global route still needs either a total computable source-visit bound, an effective complete symbolic replacement for arbitrarily many interacting visits, or a different complete decision argument. An opposing undecidability proof would require an exact reduction into the same terminal semantics; no such reduction is supplied here.

It is not enough to observe that there are finitely many k-state instances. Their positive instances have a finite maximum minimum visit count, but effectively identifying which instances are positive is exactly part of the missing decision problem. Enumerating witnesses and increasing a source-visit limit certifies positive discoveries, not termination on a negative instance.

The useful consequence is narrower: a bound proof must accommodate arithmetic synchronization of genuinely live recurrent sources even on flat graphs. Repeated visits cannot be dismissed as dead annotations or a dispensable one-visit-per-source artifact. The existing symbolic treatment of this family, rather than raw enumeration of its visits, illustrates the distinction between large witnesses and hard existence decisions.

## Sources

[1] Subtail, existing C046/C047 proof, `notes/2026-09-05-modular-synchronization.md`, pinned snapshot:
https://github.com/mhenglein/subtail/blob/f85ba3af769041349979e6130f1e2bc109b07c91/notes/2026-09-05-modular-synchronization.md

[2] Subtail, existing generator, `experiments/modular_sync_family.py`:
https://github.com/mhenglein/subtail/blob/f85ba3af769041349979e6130f1e2bc109b07c91/experiments/modular_sync_family.py

[3] Subtail, `research/problem.md`:
https://github.com/mhenglein/subtail/blob/f85ba3af769041349979e6130f1e2bc109b07c91/research/problem.md

[4] Subtail, C067/C068 source-capture proof, `notes/2026-09-09-source-capture-word-equations.md`:
https://github.com/mhenglein/subtail/blob/f85ba3af769041349979e6130f1e2bc109b07c91/notes/2026-09-09-source-capture-word-equations.md

[5] Subtail, Q004 exact statement:
https://github.com/mhenglein/subtail/blob/f85ba3af769041349979e6130f1e2bc109b07c91/research/conjectures/Q004.md

[6] Volker Diekert, Claudio Gutierrez, Christian Hagenah, *The existential theory of equations with rational constraints in free groups is PSPACE-complete*, 2001 preprint, Theorem 4 (free-monoid statement):
https://arxiv.org/html/cs/0103018v1

[7] Pierre Dusart, *Estimates of some functions over primes without R.H.*, arXiv:1002.0442v1, Theorem 5.2 and Section 6.2:
https://arxiv.org/html/1002.0442v1

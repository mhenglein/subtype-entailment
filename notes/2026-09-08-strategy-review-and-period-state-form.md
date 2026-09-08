# Strategy review, route selection, and the single-source period form

Date: 2026-09-08. Base main: `9913303` (A017 last-flag spectra checkpoint).
Workstreams: A017 (primary), A012, A008. Branch: `claude/subtail-repo-strategy-hiom63`.

**Status: strategy decision with written justification; two exact
reformulations with proofs (both are specialisations of recorded memo
statements, not new theorems); one open sub-target reduced to two explicit
proof obligations; bounded regression checks. No new decision procedure,
no new C/E identifier, no change to any evidence level. Unrestricted
Problem 1.7 remains open.**

This note answers three questions for the next researcher: which route the
accumulated evidence favours, why, and what exactly has to be proved next.
It deliberately separates what is established (with C IDs) from what is
recommended (no ID).

## 1. Where the project stands (review)

The forward chain is audited: top-free entailment reduces to PrefixAvoid and
then to BorderAvoid (C003), regular countermodels suffice (C002). Two later
results pin down the *exact* remaining problem:

* **C030/C031.** Every k-state terminal-final binary BorderAvoid instance is
  realised by a satisfiable normalised constraint system on 2k+1 variables
  with the same witness words, and terminal-final BorderAvoid is decidable
  iff normalised Problem 1.7 is (through C029 and the audited bridge).
  Hence *nothing is lost* by working only with terminal-final instances,
  and *nothing can be gained* from special structure of subtype-derived
  flags (all terminal flag patterns occur).
* **Theorem 8.9 of the memo (C012).** Decidability is equivalent to a
  computable bound on the least successful budget, equivalently on the
  length of a shortest witness as a function of k.

Everything else in the repository is either a restricted decision, a
structural lemma, or a refutation. The refutations matter for route
selection:

| Refuted target | Record | Consequence |
|---|---|---|
| Polynomial witness/budget bounds; `k-2` budgets; strict profile descent | [modular synchronisation](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/notes/2026-09-05-modular-synchronization.md) (scientific branch), Q002/Q003 | any bound must be at least `2^(Omega(sqrt k))`; simple descent arguments cannot work |
| Constant number of simultaneous loop deletions | same scientific-branch note | pumping must be *synchronised* across unboundedly many positions |
| Completeness of Necessary-budget emptiness as a NO method | [five-state all-budget NO instance](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/notes/2026-09-06-delimited-convolution.md) (scientific branch) | the NO side needs a genuinely different certificate |
| Flat edge restrictions; equal-state loop deletion; regular witness languages | C035, C019, C032 | witness sets are not regular, not CF (three equal blocks), and not covered by flat skeletons |
| Identifying suffixes by transition action / profile | recurrent-residual note | any finite quotient must keep shared word parameters |

Established positive structure for terminal instances: agreeing suffix
occurrences never merge (C036), so every suffix of an accepted word has at
most `k-1` nontrivial borders and every proper violation has overlap
exponent at most `k-1` (C038, C043). Realizable last-aligned comparison
lengths are decidable (September 7 note). Flat terminal graphs are decided
exactly (C033); single-source flags with forward-closed targets are decided
exactly (C039/C040).

## 2. Routes compared

1. **Terminal small-model theorem** (A017 target `F(k)`). Fully sufficient by
   C030/C031 and Theorem 8.9. Obstacles: superpolynomial `F`, synchronised
   pumping. Strongest partial tools exist here (C036-C040, spectra).
2. **Complete NO certificates / regular-containment decision** (A012). Also
   sufficient. The sharp form is: is a regular candidate language contained
   in a finite union of state-constrained one-use terminal-copy languages
   and bounded-power languages (September 7 decomposition note)? No general
   technique is known; generic backreference-universality results do not
   transfer, and the special shape (the copied factor is the *suffix*) is
   exactly what a reduction would have to exploit.
3. **Undecidability.** Equality of blocks is expressible ([whole-word synchronisation](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/notes/2026-09-05-word-synchronization.md), scientific branch), giving
   PSPACE-hardness, but every attempt to express a *transformation* between
   distant blocks fails because all comparisons are between a factor and a
   suffix of the *same* word at equal remaining length once a delimiter is
   present; overlap comparisons have bounded exponent (C038). A reduction
   would need unaligned copies with unbounded interaction. No gadget is
   known; this route is not recommended as the primary one but must not be
   dismissed (see Section 5).
4. **New logic or well-structured-transition-system encoding.** The witness
   condition is a `exists word, forall cuts` statement with factor
   equalities; the natural automatic structures (prefix order, equal length)
   cannot express `u = u'v` for prefixes, and the infix-order theory is
   undecidable. A WSTS needs a monotone order on "coloured tails"; literal
   residual inclusion has infinite antichains (recurrent-residual note).
   No candidate order is known.

**Decision.** Route 1, executed *bottom-up by flag structure*: first prove a
computable bound for **single-source** terminal instances (all flags leave
the start state, which is visited once), then for instances whose flags
cannot express two-directional comparisons, then general. Rationale:

* C040 shows how a single-source theorem composes: a proved-impossible
  source becomes Bad, and pruning iterates. Single-source is therefore a
  building block, not a dead-end special case.
* Every known hard family needs flags in *both* comparison directions
  (Section 4). Single flags, and more generally one-directional flag
  patterns, cannot force equalities, which is the mechanism behind the
  superpolynomial lower bounds.
* Single-source is precisely Anderson et al.'s unbordered-word problem with
  coloured borders (Section 3), for which a `6n+1` bound is known in the
  uncoloured case and C039 gives the forward-closed coloured case. The
  missing colour bookkeeping is a concrete combinatorial task, not a
  search for a new idea.

## 3. Two exact forms (proofs; specialisations of Proposition 8.2)

Fix a partial deterministic binary automaton with start `q0`, flags `G`,
Bad, accepting states, an accepted word `w` of length `n` with run
`c(0..n)`, and write `rho = reverse(w)`, `c'(x) = c(n-x)`.

**Shift form.** Let `Z(s)`, for `1 <= s <= n`, be the length of the longest
common prefix of `rho` and `rho[s:]` (the Z-array). Then `w` is a witness iff
it is admissible, no visited state is diagonally flagged, and

    for every 1 <= s <= n and every 0 <= t <= Z(s):  not G(c'(s+t), c'(t)).

*Proof.* A proper flagged agreement is a pair `i < j <= n` with
`w[j:]` a prefix of `w[i:]`. Put `s = j-i >= 1` and `t = n-j >= 0`. Then
`c(i) = c'(s+t)`, `c(j) = c'(t)`, and `w[j:]` is a prefix of `w[i:]` iff
`rho[0..t) = rho[s..s+t)` iff `t <= Z(s)`. Conversely each `(s,t)` with
`t <= Z(s)` gives such a pair. Diagonal pairs are the `i = j` case. This is
Proposition 8.2 (OCC) with `d = s`, `l = t`; it is recorded here because the
Z-array makes the "one common word" constraint explicit: all shifts compare
the same word with its own prefix.

Two consequences of C036 in this language, for terminal instances: the
pairs `(c'(s+t), c'(t))` along one shift are pairwise distinct in both
coordinates, and at every position `m` the number of shifts `s <= m` with
`Z(s) >= m-s` (the live borders of `rho[1..m]`) is at most `k-1`.

**Single-source period form.** Suppose every flag has the form `(q0, q)` and
`q0` has no incoming transition (C039 justifies deleting positive returns to
the start for existence questions). Let `T = { q : (q0,q) in G }`. Then an
accepted word `w` is a witness iff `q0` is not in `T`, the final state is not
in `T`, and

    for every period d of w with 0 < d < n:  c(d) not in T.

*Proof.* With `i = 0` the shift form says `w[j:]` is a prefix of `w` iff `w`
has period `j` (Lemma 5.2), and the flagged pair is `(c(0), c(j)) = (q0, c(j))`.
The empty suffix `j = n` gives the final-state condition, `j = 0` the
diagonal condition. No other flags exist.

So a single-source witness is an accepted word *none of whose periods lands
on a T-state of its own run*. For `T` = all nonfinal states this is
exactly "unbordered"; Anderson et al. prove that if such a word exists in an
`n`-state NFA language then one of length at most `6n+1` exists.

**C038 at `i = 0`.** If `w` is a single-source witness with minimal period
`d0 <= n/2`, write `w = x^e x'` with `|x| = d0`, `x` primitive, `x'` a proper
prefix of `x`. The states `r_j = c(j d0)`, `0 <= j <= e`, are pairwise
distinct, hence `e <= k-1` and `n < k d0`. (Determinism plus terminality:
a repeated `r_i = r_j` would make the run periodic from `i` on, so the
terminal accepting state would be entered before the end.) This is the
`i = 0` instance of C038 and is *not* new; it is restated because it splits
the single-source problem into the two regimes below. The `x^e x'`
shape also shows that the deletion of a block of full periods, which one
might hope to use, never applies to accepted words: no repetition exists.

## 4. Flag directions and the bounded census

The scientific branch's whole-word synchronisation gadget flags a boundary with predecessor tag `a`
against a boundary with tag `b` for *both* orders `(a,b) = (0,1)` and
`(1,0)`. With only one order, the same argument gives a one-directional
statement: if the earlier block `u` and the final block `v` differ, let `x`
be their longest common suffix; the flag fires only when the letters before
`x` are `0` in `u` and `1` in `v`. Hence a one-directional flag pattern
expresses "`u` is not smaller than `v` in the colexicographic order at the
first difference from the right", never `u = v`. The scientific branch's modular family
likewise needs `p_i + p_r` flags per block pair, one set forbidding `n_i < n_r`
and one forbidding `n_i > n_r`. Every recorded hard family therefore uses
two-directional comparison. This is an observation about known
constructions, not a theorem that one-directional patterns are easy.

Bounded data (`python3 experiments/check_period_state_form.py`, seed
`2026090801`, saved in `results/period-state-form.json`):

* All 13,800 four-state terminal instances (start 0, terminal final 3, every
  valid partial table) with exactly one off-diagonal nonfinal flag: shortest
  witness lengths 1 to 4; 28 finite languages without a witness; 660 searches
  reached the cap 12 and are UNKNOWN (C034 decides them all, and shows they
  are NO). All 34,500 such instances with two flags: the same maximum 4.
  The longest shortest witness, `1101`, is a single-source instance.
* Random five- and six-state samples with one, two, or three flags (150
  instances each, cap 14) found longest shortest witnesses of lengths 4, 5,
  5 and 5, 5, 5. Separate hill-climbing runs (not part of the saved result)
  reached 6 to 9 for `k = 6..8` with one to four flags, far below the known
  12 (C020, six states) and 14 (the eight-state modular example) that need many flags.
  These are lower bounds from weak searches and support nothing beyond the
  hypothesis worth testing next.
* 76,500 word comparisons on 300 random instances (terminal and not,
  with Bad states) agree between the shift form and both recorded witness
  predicates; 102,000 comparisons on 400 random single-source instances agree
  between the period form and the direct predicate; all 18 periodic shortest
  witnesses found satisfy the C038 exponent bound.

## 5. What has to be proved next (handoff)

**Target theorem (single-source).** For a terminal `k`-state automaton with
start visited once and target set `T`, if a `T`-period-free accepted word
exists then one exists of length at most a computable `F1(k)`; conjecturally
linear, as in Anderson's `6n+1`.

Take a shortest such `w` of length `N` with minimal period `d0`.

*Regime B, `d0 <= N/2`.* By Section 3, `w = x^e x'` with `e <= k-1`, so it
suffices to bound `|x|`. The obligation is a **synchronised loop deletion
inside `x`**: for `|x| > 2 k^{k}` the `(e+1)`-tuple of run states at equal
offsets in all copies repeats at offsets `a < b` lying either both inside
`[0,|x'|)` or both inside `[|x'|,|x|)`; deleting `[a,b)` from every copy keeps
the word accepted and the multiples of the new period on the same states.
What remains is the *creation analysis*: the shortened word `y^e y'` may (i)
have a non-primitive `y`, creating new period positions, or (ii) acquire a
border shorter than `|y|` that reaches across the deletion junction whose
end-distance state lies in `T`. Both effects are local to the junction; the
proof must show that among the many admissible offset pairs some avoids
both. Until this is done, no bound on `|x|` is claimed.

*Regime A, `d0 > N/2`.* All borders are shorter than `N/2`. Run the proof of
Anderson et al. Theorem 58 with "bordered" replaced by "has a border whose
end-distance state is in `T`": Claims 59-61 go through verbatim for the word
combinatorics and produce a border `alpha` of `w` with `|alpha| <= n`; what
is missing is that the state at distance `|alpha|` from the end is in `T`.
C039 obtains it from forward closure of `T`. Without closure one must track
the phase of `alpha` inside the `x`-periodic ends `Psi_L = h x^k p`,
`Psi_R = x^k p g` and relate the state at its start to the known `T`-states
at the starts of the long borders `b_1`, `b_2`. This is the second
obligation.

**Then.** Extend from the start state to an arbitrary single source `p`
(C040 already reduces to suffixes from `p`), then to flag patterns whose
sources and targets admit no two-directional comparison, then general.
Any bound obtained must be checked against the modular superpolynomial family
before it is stated for the general case.

**Do not.** Do not treat the census maxima as bounds; do not assume the
exponent lemma bounds `d0`; do not restart profile-descent or equal-state
deletion; do not read the shift form as a finite quotient of words (the
recurrent-residual counterexamples apply unchanged).

## 6. Independent check and limits

The Z-array implementation is a third, independently written witness
predicate; it agrees with `witness` and `border_witness` on every tested
word. The period form is checked against `witness` only. No independent
mathematical review of Sections 3-5 has taken place. No Lean statement was
added. The hill-climbing figures are reported for orientation only and are
not part of the saved result.

# Single-source terminal BorderAvoid: junction lemma, shape lemmas, and the remaining root-length obligation

Date: 2026-09-08. Base main: `9913303`. Workstream: A017 (single-source
sub-target of the strategy note). Branch `claude/subtail-repo-strategy-hiom63`.

**Status: written all-length proofs (Lemmas 1-5 and the Theorem), an exact
exhaustive census for four and five states, and bounded lower-bound searches.
No independent mathematical review, not Lean-checked. The single-source
problem is NOT decided here: one explicit obligation remains (Section 6). No
new C/E identifiers are allocated; this note is a scoped continuation of the
[strategy note](2026-09-08-strategy-review-and-period-state-form.md).**

## 1. Setting

`M = (Q, delta, p, f)` is a partial deterministic binary automaton with
`n = |Q|` states, start `p` with no incoming transition, and a single
accepting state `f` that is terminal (no outgoing transition). Every accepted
word therefore visits `p` exactly at position 0 and `f` exactly at its end;
all other positions carry states in `Q \ {p,f}`, a set of size `n-2`.
Fix `T subseteq Q \ {p,f}`.

For an accepted word `w` of length `N` with run `c(0..N)`, a **T-period** is
an integer `d` with `1 <= d < N`, `w[i] = w[i+d]` for all `0 <= i < N-d`, and
`c(d) in T`. A **witness** is an accepted word without T-period. By the
period form of the strategy note this is exactly the BorderAvoid witness
notion for the flag set `G = {(p,q) : q in T}`, and C039/C040 show that the
positive-return-free assumption on `p` is harmless for existence questions.

Notation: `z^omega[a:b]` is the factor of the infinite word `z z z ...`
occupying positions `a <= i < b`. A word is `d`-periodic when it has period
`d`. A nonempty word is primitive when it is not a proper power. Two
standard facts are used: (FW) if a word of length at least `d0 + d` has
periods `d0` and `d` then it has period `gcd(d0,d)` (Fine-Wilf); (PR) for a
primitive `z0` of length `d0`, `z0^omega[a:a+d0] = z0^omega[b:b+d0]` implies
`a = b (mod d0)`.

Throughout, `w` is a **shortest** witness and `N > 2n`.

**Loop deletion.** For `x < y` with `c(x) = c(y)` put
`w^{xy} := w[0..x) w[y..N)` and `delta := y - x`. It is accepted, its run is
`c(i)` for `i <= x` and `c(i+delta)` for `i >= x`, and it is shorter than
`w`; by minimality it has a T-period.

**Border count (C036 at `i=0`).** For an accepted word, distinct borders
`b_1 > b_2` have distinct start states `c(N-b_1) != c(N-b_2)`: otherwise
reading the common border word `w[0..b_2)` from both positions would reach
the terminal `f` before the end of the word. Hence an accepted word has at
most `n-2` nontrivial borders, i.e. at most `n-2` periods in `[1,N)`.

## 2. Lemma 1 (junction lemma)

Let `d` be a T-period of `w^{xy}` and `b := |w^{xy}| - d` the corresponding
border length. Exactly one of the following holds.

* **(L)** `d > x`. Then `x < b < N - y`,
  `w[N-b..N) = w[0..x) w[y..y+b-x)`, and `c(N-b) in T`.
* **(S)** `d <= x`. Then `c(d) in T`, `w^{xy}` is `d`-periodic, and `w` is
  not `d`-periodic.

*Proof.* If `d > x` the T-state is `c^{xy}(d) = c(d+delta)`, and
`d + delta = N - b`. The border word is
`w^{xy}[0..b) = w^{xy}[d..) = w[d+delta..N) = w[N-b..N)`; since `d > x`,
`b < |w^{xy}| - x = N - y`. If `b <= x` then `w^{xy}[0..b) = w[0..b)`, so `b`
is a border of `w` whose period `N-b` has state `c(N-b) in T`: `w` would have
a T-period. Hence `b > x` and `w^{xy}[0..b) = w[0..x) w[y..y+b-x)`. If
`d <= x` the T-state is `c(d)`; `w^{xy}` is `d`-periodic by assumption; and if
`w` were `d`-periodic, `d < N` would be a T-period of `w`. QED

## 3. Lemma 2 (end loops are always of type (S))

Positions `N-n, ..., N-2` carry `n-1` states from the `(n-2)`-element set
`Q \ {p,f}`, so there are `N-n <= x < y <= N-1` with `c(x) = c(y)`. Call such
a pair an **end loop**; its tail `w[y..N)` is nonempty and shorter than `n`.
Symmetrically positions `1, ..., n` give a **start loop** `1 <= x0 < y0 <= n`.

For an end loop, every T-period of `w^{xy}` is of type (S): type (L) would
need `x < b < N - y <= n - 1 < N - n <= x`. QED

## 4. Lemma 3 (periodic ends restrict periods)

**Lemma 3.** Let `W` be a word, `z0` primitive of length `d0`, and suppose
`W[0..X) = z0^omega[0:X]` with `X >= d0`, while `W` is not `d0`-periodic.
Then every period `d` of `W` satisfies `d > X - d0`.

*Proof.* Let `d <= X - d0` be a period. Comparing `W[0..X-d)` with
`W[d..X)` inside the periodic prefix, where the overlap `X-d` is at least
`d0`, (PR) gives `d = 0 (mod d0)`. Then `W` is `d`-periodic with
`W[0..d) = z0^{d/d0}`, so `W` is a prefix of `z0^omega`, i.e. `d0`-periodic,
a contradiction. QED

**Lemma 3'.** Symmetrically, if the suffix `W[|W|-Y..)` of length `Y >= d0`
is a factor of `z0^omega` and `W` is not `d0`-periodic, then every period `d`
of `W` satisfies `d > Y - d0`. (Same proof on the suffix; the last `d`
letters are then a power of a conjugate of `z0`, so `W` is a suffix of a
power of that conjugate and hence `d0`-periodic.)

In terms of borders: all borders of such a `W` are shorter than
`|W| - X + d0` (respectively `|W| - Y + d0`).

## 5. Lemmas 4 and 5 (small primitive roots force short witnesses)

**Lemma 4 (end loop with small root).** Let `[x,y)` be an end loop, `d'` a
T-period of `w^{xy}` (type (S) by Lemma 2), `z := w[0..d')`, and `z0` the
primitive root of `z`, `d0 := |z0|`. If `d0 <= n` then `N <= n^2 + 6n`.

*Proof.* `w^{xy}` is `d'`-periodic with prefix `z`, hence a prefix of
`z^omega = z0^omega`. So `w[0..x) = z0^omega[0:x]` with `x >= N - n >= d0`,
and the tail is `w[y..N) = z0^omega[x : x+N-y]`. Write `m := w[x..y)`,
`1 <= |m| <= n-1`, and `t := w[y..N)`, `1 <= |t| <= n-1`; so
`w = z0^omega[0:x] m t`. `w` is not `d0`-periodic: otherwise it would be
`d'`-periodic (`d0 | d'`, `d' <= x < N`) with `c(d') in T`. By Lemma 3 every
border of `w` is shorter than `N - x + d0 <= n + d0`.

Assume `N > n^2 + 6n`. The positions `r, r+d0, r+2d0, ...` of the interval
`[n+d0, x-n-d0]` number more than `n-1` when `x - 2n - 2d0 >= (n+1)d0`,
which holds because `x >= N-n > n^2 + 5n >= (n+3)d0 + 2n`. Their states lie in
`Q \ {p,f}`, so two of them coincide: `c(a) = c(a'')` with
`n + d0 <= a < a'' <= x - n - d0` and `a'' - a = j d0`. Delete `[a,a'')`:

    w''' := w[0..a) w[a''..N) = z0^omega[0 : x - j d0] m t,

because removing whole periods from inside a prefix of `z0^omega` leaves a
prefix of `z0^omega`. It is accepted and shorter. It is not `d0`-periodic:
`d0`-periodicity of `w'''` says `m t = z0^omega[x - j d0 : x - j d0 + |mt|]`,
which equals `z0^omega[x : x + |mt|]`, i.e. `d0`-periodicity of `w`. By
Lemma 3 (with `X = x - j d0 >= d0`) every border of `w'''` is shorter than
`|w'''| - (x - j d0) + d0 = N - x + d0 <= n + d0`.

Let `b < n + d0` be a border of `w'''`. Its prefix occurrence
`w'''[0..b) = w[0..b)` since `b <= a`; its suffix occurrence is the last `b`
letters of `w'''`, which are the last `b` letters of `w` since the deletion
ends at `a'' <= N - n - d0`; and the run of `w'''` after position `a` equals
the run of `w` after `a''`, so the state at distance `b` from the end is the
same in both words. Hence `b` is a border of `w` with the same start state,
which is not in `T` because `w` is a witness. Therefore `w'''` has no
T-period, contradicting the minimality of `w`. QED

**Lemma 5 (start loop of type (S)).** Let `[x0,y0)` be a start loop
(`1 <= x0 < y0 <= n`) and suppose some T-period `d'` of `w^{x0 y0}` is of
type (S). Then `N <= n^2 + 6n`.

*Proof.* Now `d' <= x0 < n`. With `z := w[0..d')`, root `z0`, `d0 := |z0| <=
d' < n`: `w^{x0y0}` is a prefix of `z0^omega`, so `w[0..x0) = z0^omega[0:x0]`
and `w[y0..N) = z0^omega[x0 : x0 + N - y0]`, a factor of `z0^omega` of length
`L := N - y0 >= N - n >= d0`. Put `m := w[x0..y0)`. `w` is not `d0`-periodic
(else `d'` would be a T-period). By Lemma 3' every border of `w` is shorter
than `N - L + d0 = y0 + d0 <= n + d0`.

Assume `N > n^2 + 6n`. Inside `[y0 + n + d0, N - n - d0]`, whose length
exceeds `(n+1) d0` because `N - y0 - 2n - 2d0 >= N - 3n - 2n > n^2 + n >=
(n+1)d0`, choose `a < a''` congruent modulo `d0` with `c(a) = c(a'')` and
delete `[a,a'')`. The result `w''' = z0^omega[0:x0] m z0^omega[x0 : x0 + L']`
with `L' = L - (a''-a) >= d0` is accepted, shorter, and not `d0`-periodic
(its `d0`-periodicity is the statement `m z0^omega[x0:x0+L'] =
z0^omega[x0 : x0+|m|+L']`, which forces `m = z0^omega[x0:x0+|m|]` and
`|m| = 0 (mod d0)`, exactly the conditions for `w`). By Lemma 3' its borders
are shorter than `y0 + d0 <= n + d0`, and as in Lemma 4 each such border is a
border of `w` with the same start state: prefix occurrences lie before `a`,
suffix occurrences after `a''`, and the run after `a` in `w'''` is the run
after `a''` in `w`. So `w'''` is a shorter witness, a contradiction. QED

## 6. Theorem (shape of a long shortest single-source witness)

**Theorem.** Let `w` be a shortest single-source witness with `N > n^2 + 6n`.
Fix an end loop `[x,y)` and a T-period `d'` of `w^{xy}`; let `z0` be the
primitive root of `w[0..d')`, `d0 := |z0|`. Then:

1. `d' <= x`, `c(d') in T`, and `d0 > n`;
2. `w = z0^omega[0:x] m t` with `m = w[x..y)`, `t = w[y..N) =
   z0^omega[x : x+N-y]`, `1 <= |m|, |t| <= n-1`; `w` is not `d0`-periodic,
   and every border of `w` is shorter than `n + d0`;
3. the number of full periods `e0 := floor(x/d0)` satisfies `e0 <= n+1`;
   consequently `N < (n+2) d0 + n`;
4. every start loop `[x0,y0)` has only type-(L) T-periods: there is
   `b' in (x0, N-y0)` with `w[N-b'..N) = w[0..x0) w[y0..y0+b'-x0)` and
   `c(N-b') in T`.

*Proof.* (1) Lemma 2 gives type (S), Lemma 4 gives `d0 > n`. (2) is the
structure derived in the proof of Lemma 4 together with Lemma 3. (3) The
states `c(i d0)` for `2 <= i <= e0 - 2` lie in `Q \ {p,f}`; if `e0 >= n+2`
two of them coincide, and deleting the corresponding block of whole periods
(which starts at `a >= 2 d0 >= n + d0` and ends at `a'' <= (e0-2) d0 <= x -
2 d0 <= N - n - d0`) produces, exactly as in Lemma 4, a shorter word with the
same borders and border states, hence a shorter witness. So `e0 <= n+1`, and
`N - n <= x < (e0 + 1) d0 <= (n+2) d0`. (4) is Lemma 5. QED

**What is and is not proved.** The theorem reduces a computable bound
`F1(n)` for single-source instances to a computable bound on the length
`d0` of a primitive word `z0` in the configuration of item 2: a shortest
witness longer than `n^2 + 6n` is a prefix of `z0^omega` of at most `n+2`
periods, followed by a defect `m` and a tail `t` of fewer than `n` letters
each, with `t` continuing the phase of the periodic prefix, `m` breaking it,
and a T-state at some multiple `d' = k d0 <= x` of the root length.

The natural attack is a synchronised window deletion inside `z0`. Write
`xi := x mod d0` for the phase at which the periodic prefix ends. For `d0`
large enough (explicitly `d0 > (n+3)(n^{n+3} + 3n)` suffices) there are two
offsets `phi < phi'` in `[0,d0)`, both outside the `3n` phases
`[xi - 2n, xi + n]` and on the same side of `xi`, at which the run states of
all `e0 + 1` copies coincide simultaneously. Deleting the window
`[phi,phi')` from every copy gives an accepted shorter word
`w~ = z~^omega[0:x~] m t` of the same shape with root `z~`, `|z~| = d0 -
(phi' - phi) > n`. Because the window avoids the phases occupied by `m t`
and by the letters just before `xi`, the condition "`w~` is `|z~|`-periodic"
is literally the condition "`w` is `d0`-periodic" and therefore fails.
Two steps are missing:

1. **Primitivity.** Lemma 3 needs `z~` primitive. If `z~` is a proper power
   `z1^r`, the shortened word can still be `|z1|`-periodic, with a T-state at
   a multiple of `|z1|`, and no contradiction follows. Needed: a lemma
   bounding the number of windows that turn the primitive `z0` into a proper
   power, or a choice of window avoiding them.
2. **Border correspondence.** In Lemmas 4 and 5 the deletion left the first
   `n + d0` letters and the last `n + d0` letters untouched, so borders and
   their start states transferred verbatim. A window deleted from every
   copy changes the prefix of `z0`. Borders of the new word are the lengths
   `r + |mt|` with `r < |z~|` such that the length-`r` prefix of `z~` equals
   the `r` letters preceding phase `x~` and `m t` occurs at phase `r` in the
   cyclic word `z~`; their start states sit at distance `r` before `x~`.
   Needed: show that some admissible window creates no such border whose
   start state is in `T`, using that none exists for `w` itself and that at
   most `|mt|` occurrences of `m t` can be created across the junction.

Either a proof of both steps or a different surgery would complete the
single-source bound. Until then the single-source problem stays open.

## 7. Exact census and bounded lower bounds

`python3 experiments/single_source_census.py K` enumerates every valid
single-source table with `K` states up to relabelling of the middle states
and every nonempty target set, searches a shortest witness by breadth-first
search over defined runs up to length 20, and certifies NO only by an
exhausted Necessary automaton at some budget `L, D <= 3`. Saved result:
[results/single-source-census.json](../results/single-source-census.json).

| States | Canonical tables | Instances | Shortest-witness lengths (count) | NO | finite, none | UNKNOWN |
|---:|---:|---:|---|---:|---:|---:|
| 4 | 414 | 1,242 | 1 (354), 2 (456), 3 (330), 4 (8) | 77 | 17 | 0 |
| 5 | 10,109 | 70,763 | 1 (16,100), 2 (23,554), 3 (18,466), 4 (8,446), 5 (456), 6 (8) | 3,513 | 220 | 0 |

Every instance is decided; the longest shortest witness has length 4 for
four states and 6 for five states. One five-state extremal instance is the
path `0 -1-> 1 -1-> 2 -1-> 3`, `3 -0-> 2`, `3 -1-> 4 = f`, `T = {1}`: its
accepted words are `111(01)^m 1`; the shortest, `1111`, has the T-period 1,
and `111011` is the shortest witness. The `n^2 + 6n` threshold of the
Theorem (22 and 55) is far above both maxima, so the census cannot test the
Theorem's mechanism; it tests only its conclusion.

A hill-climbing search over six-state single-source instances (scratch run,
seed 7, 8 restarts of 600 mutations, cap 24; not part of the saved result)
found a shortest witness of length 8: table `0:(1,-) 1:(4,-) 2:(5,4) 3:(2,1)
4:(3,-)`, final 5, `T = {1}`, witness `00001000`. Together with the exact
values 4 and 6 this matches `2n - 4` for `n = 4, 5, 6`; the six-state value
is a lower bound only, and no formula is conjectured beyond noting the
coincidence with the C021 budget-growth pattern.

Hill-climbing searches over single-source instances (scratch runs with a
fixed seed, 8 restarts of 600 mutations each, cap 24; not part of the saved
result) found shortest witnesses of length 8 for six states, 10 for seven
states, and 10 for eight states. These are lower bounds from a weak search.
Together with the exact values 4 and 6 they are consistent with, but do not
establish, a linear maximum such as `2n - 4`.

## 8. Independent check and limits

The census uses the direct witness predicate `border_lab.witness` and the
recorded Necessary automaton; the two agree by E001/E002. The lemmas above
are written proofs and have not been reviewed by anyone else; the constants
in the thresholds were chosen generously and not optimised. Nothing here
changes the status of any recorded claim.

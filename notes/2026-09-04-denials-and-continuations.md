# Denials, periodic continuations, and the finite-terminal remainder

Date: 2026-09-04. Continues A010/A013 after commit e93f035.

**Status: WRITTEN PROOF + REPRO, not Lean-checked.** No unrestricted decision
for Problem 1.7 is claimed. Infinite *safe continuation of a separating path*
is not the same distinction as finite versus infinite *type trees*.
The normalized subtype transfer uses the existing forward bridge; the new
independent implementation is checked against exact regular countermodels.

## 1. Denial safety needs no separate subset component (C025)

Let W be the propagation system of a satisfiable normalized constraint set,
BF its forced-root variables, and D its bottom-denial variables. Every push
has target in BF. Satisfiability therefore implies that no configuration
(f,epsilon), f in BF, reaches any (d,z), d in D.

**Lemma.** If (x,w) reaches (d,z), d in D, then w=u z for a prefix u of w,
and (x,u) reaches (d,epsilon).

**Proof.** Consider the minimum stack height of the run. If the final height
were larger, take the last visit to that minimum and the first subsequent
push. Its target f is in BF. The pushed letter and the residual stack below
it can never be popped afterward, or the run would revisit its minimum.
Strip this unchanged suffix from the rest of the run. This gives a run from
(f,epsilon) to a denial, contradicting satisfiability. Thus the final stack
height is the minimum. The final residual z is unchanged throughout the run;
stripping it gives the claimed pop-summary run. Conversely, any such pop run
can be carried out above an unchanged residual stack.

Consequently the denial-predecessor language is exactly

    Union_{d in D} Pop_W(x,d) Sigma*.

With B(u) the usual W pop-summary subset from alpha, the every-prefix seed
safety condition is exactly

    for every u prefix of p: B(u) intersects D = empty.

Keep only the paired B/A subsets, mark a state Bad iff its B component meets
D, and retain the existing F and G definitions. The resulting instance has
the same witness language as the full B/A/S construction. The satisfiability
guard is essential; this argument must not be applied to inconsistent input.
This is a construction-level proof, not a Lean formalization of saturation.

## 2. Exact continuation after a supplied prefix (C026)

Let I be an annotated automaton satisfying the established absorption law:
every defined successor of a final state is final and has no incoming flag.
Let Z be the final states with empty incoming flag columns. Delete Bad states
and diagonal-flagged states when discussing safe paths.

Fix a safe prefix v of length n ending in Z. All later target states have
empty flag columns, so only pairs i<j<n can remain problematic. A pair which
already mismatches in v never becomes an agreement after extension. Each
still-active pair has d=j-i and forces exactly one infinite periodic future:

    v[i:j]^omega, phased by (n-i) modulo d at the end of v.

Reduce the rotated period to its primitive root and merge duplicate futures.
Call the finite collection R(v). For every finite continuation x,

    vx is a witness iff x is safe and is not a prefix of any ray in R(v).

Indeed, the suffix comparison is a period-d equality beginning at i. Each
new letter must match that ray for the comparison to survive. There are no
new flagged targets after n, and all diagonal/boundary obligations were
handled by safety and membership in Z.

This gives an exact finite product: current automaton state, and the surviving
rays with their current phases. Reading a mismatching letter permanently
removes that ray. An empty collection is success. Exhaustion is NO_EXTENSION
for the **supplied prefix only**. A state cap is UNKNOWN. A crude bound on
product size is k times the product of (d+1) over initial ray periods d.
It is finite, but depends on v, which may be arbitrarily long.

A finite entry-frontier procedure is therefore complete when the safe
pre-Z region is acyclic. It must also check final non-Z prefixes directly,
including terminal accepting states. On a pre-Z cycle, skipping the repeated
state is only an incomplete search and must leave UNKNOWN.

## 3. A cubic-size branching certificate (C027)

Suppose a safe reachable vertex q in Z lies on a cycle and has two distinct
safe outgoing letters. The second edge may leave the cycle, even to a terminal
state. Take a shortest safe prefix v to q, n<=k-1, and a nonempty cycle u at q
of length at most k. Let a be its first letter and choose another safe outgoing
letter b. There are at most r<=n(n-1)/2 active rays after v.

The r+1 tails u^j b, 0<=j<=r, are pairwise prefix-incomparable: at the first
exit position the shorter tail reads b and the longer reads a. Each infinite
ray can cover at most one of them. At least one tail defeats all r rays and
produces a witness of length at most

    n + r |u| + 1 <= k-1 + k (k-1)(k-2)/2 + 1.

If there are no active rays, v itself suffices. Absence of such a vertex is
not a NO certificate. Instead it means the reachable safe Z graph has only
finitely many maximal continuations: finite terminal paths and ultimately
periodic rays. Before a cycle a path has no repeated vertex; on a cycle every
vertex has exactly one safe outgoing letter. Each ray has a simple lasso
with stem plus cycle length at most k.

## 4. Exact decision for infinitely extendable witnesses (C029)

The following decides whether there exists a witness whose endpoint admits
an infinite safe path. A negative verdict is **NO_INFINITE_EXTENSION**, not
NO for unrestricted entailment.

First restrict the safe Z graph to vertices that can reach a cycle. If the
branching certificate applies in this restriction, its selected continuation
also admits an infinite safe future. Otherwise all infinite tails from each
reachable Z state have finitely many simple lasso descriptions t u^omega.

Every active prediction from Section 2 is purely periodic. A non-purely-periodic
lasso differs from each of finitely many predictions, so after a finite prefix
of that lasso all comparisons are broken. Any safe entry prefix to its starting
state therefore yields a witness. This case needs no bound on earlier paths.

It remains to handle pure tails p^omega, with p primitive and |p|=d<=k.
For a fixed Z state q and fixed p, we can decide existence of an arbitrary-
length safe prefix v ending at q for which p is not in R(v).

### Finite periodic-suffix monitor

Two suffixes of the infinite word v p^omega beginning at i<j are equal iff:

1. both positions lie within its maximal final p-periodic part; and
2. j-i is divisible by the primitive period d.

For the forward implication, equal suffixes make the suffix at i periodic
with period j-i. Its eventual primitive period d divides j-i. Equality then
propagates the eventual p phase backwards to i. The reverse implication is
immediate from periodicity. Thus a forbidden ray p is active exactly when
there is an ordered flagged state pair in the final matching segment whose
positions are congruent modulo d.

Enumerate the possible residue h=|v| modulo d. While reading v left to right,
compare its letter at position t with p[(t-h) modulo d]. Maintain the original
state, t modulo d, sets of states seen in the current matching segment for
each residue class, and a conflict bit. On a match, add the new state to its
residue bucket and test incoming flags from earlier states in that bucket.
On a mismatch, reset all buckets and the conflict bit, then seed the current
state. Reject globally unsafe states. Accept at q when t modulo d=h and the
conflict bit is false.

This is a finite automaton with at most 2 k d 2^(kd) states for each h. It
handles **unbounded pre-acceptance loops**, unlike simple-prefix enumeration.
If it accepts v, append p until all remaining rays have mismatched. Since p
itself is absent, this terminates. Conversely an infinitely extendable witness
can be continued into Z; its prefix there has no active ray and is accepted
for the corresponding pure tail. These implications prove completeness.

Resource caps preserve UNKNOWN. Without caps this is a terminating exact
procedure for the stated category. A generous uniform witness-length bound
for that category is

    H_infinity(k) = 2 k^2 (k+1) 2^(k^2),  k>=1.

For the monitor case, a shortest accepted prefix has n<2 k d 2^(kd) states
of history. A different ray with period d'<n disagrees with p within dd'
letters (otherwise the pair of periodic positions repeats without a mismatch).
Thus at most dn further letters kill every ray. The branching and non-pure
lasso cases have smaller bounds. This is not a bound for terminal witnesses.

## 5. An actual subtype obstruction to deleting pre-final loops (C028)

Use eight variables alpha, beta, b, a1, a2, a3, z, r, and the constraints

    b x alpha <= beta       b x z <= beta
    b x r <= z              r x b <= r
    alpha <= b x a1         a1 <= b x a2
    a2 <= a2 x a3           a3 <= b x b
    b <= bottom.

Ask whether alpha<=beta. This system is satisfiable. Its exact separating-
path language, meaning paths separable by some satisfying assignment, is

    { 11 0^n 1 : n>=1 }.

Here is an all-length argument. The upper constraints and b=bottom permit
alpha product nodes only at epsilon, 1, 11 0*, and 11 0*1. The lower constraints
force r at every 0^n, then z at epsilon and 1 0*, and beta at epsilon, 1, and
11 0*. Thus only 11 0^n1 can separate. The n=0 candidate 111 cannot: alpha
having 111 forces its prefix 11, and b x alpha<=beta puts 111 in beta.
For n>=1 seed precisely the prefixes of 11 0^n1 in alpha, take the least
upper-constraint closures of a1,a2,a3, take r=0*, z={epsilon} union 1 0*, and
beta={epsilon} union 1 X(alpha) union 1 X(z). This assignment satisfies every
constraint and beta lacks 11 0^n1: its required alpha suffix 1 0^n1 is not a
prefix of the chosen alpha path, and its z suffix is outside 1 0*.

The reduced paired automaton has seven states. The prefixes 11 and 110 reach
the same state. The shortest witness is 1101; deleting that loop produces
111, which is not a witness. Every separating path is a terminal safe path:
the final a3 child cannot itself have a product child because a3<=b x b.
The instance therefore has witnesses but NO_INFINITE_EXTENSION. The type
assignment still includes infinite r=0*; this is not a finite-tree result.

## 6. Precise remaining problem

For absorbing instances, every safe extension of a witness is again a witness.
If a witness endpoint has no infinite safe continuation, its finite reachable
safe graph is acyclic and it extends to a terminal safe witness in at most k-1
additional letters. Consequently witness existence is exactly the disjunction:

    infinitely extendable witness, OR terminal safe witness.

The first alternative is now decided by Section 4. The second is not decided
in general by this work. It involves arbitrarily long pre-final paths followed
by a finite terminal continuation. Section 5 proves that deleting repeated
pre-final states is unsound even for actual subtype outputs. The next target
is a complete decision or a computable witness bound for this terminal branch,
not another blanket padding argument.

## 7. Reproduction and limitations

Run from the repository root:

    python3 experiments/check_unrestricted_continuation.py
    python3 experiments/check_infinite_extensions.py

The first uses 500 generated normalized systems: 383 SAT and 117 UNSAT;
24,129 full/reduced/exact-canonical-model comparisons; 24,129 safety comparisons;
45,615 periodic-prediction comparisons; 211 validated branching certificates;
and all 2,047 binary words through length ten for the actual obstruction.
A separate periodic example checks a genuine NO_EXTENSION by an independent
complete necessary-automaton search with a fixed-prefix filter.

The second uses 1,500 absorbing abstract instances and 400 additional generated
subtype systems; 305,010 monitor-identity checks; 502 exact small-state oracle
comparisons; and 18,207 additional subtype word comparisons. Every returned
subtype witness is checked by exact regular-language model operations.
No resource caps occurred in the saved runs. Written proofs, not these finite
samples, establish the quantified results. No Lean proof or full original
repository test rerun is asserted here. No literature-priority claim is made.

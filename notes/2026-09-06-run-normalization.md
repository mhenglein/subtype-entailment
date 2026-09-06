# Exact run normalization for every binary terminal instance

Date: 2026-09-06. Parent: `df54d87ec4432f489d0b845c7834612f6af70c12` (PR #9).
Approaches A008/A017. Proposed claims C054-C055. Experiment E035.

**Status: written all-length proofs and executed finite checks; independent
review requested; not Lean-checked.** This note does not claim an unrestricted
solution of Problem 1.7. Unlike the previous marker certificates, its main
normalization theorem applies to EVERY binary terminal instance. It bounds
run lengths in terms of the number of runs; it does not bound that number.
No literature-priority claim is made.

## 1. Statement (C054)

Let M be a k-state partial deterministic binary automaton, all of whose
accepting states are terminal. A defined accepted word w has canonical maximal
homogeneous runs

    w = a_0^n_0 ... a_(r-1)^n_(r-1),
    n_i>0, a_i in {0,1}, a_i != a_(i+1).

For a defined accepted word x, let

    A(x) = {(c(i),c(j)): 0<=i<=j<=|x| and x[j:] prefixes x[i:]}.

This includes diagonal and empty-suffix comparisons. The annotation-free
profile determines all flag obligations, while the visited-state set determines
Bad-state avoidance.

Complete each one-letter transition to a function f_a on k+1 states by adding
an absorbing undefined/dead state. Let P_a be the least common multiple of
its cycle lengths. Set

    H = (k+1)^2,   P = max(P_0,P_1).

There is an effective, polynomial-time transformation of the run-length
encoding of w to a word v with exactly the same r runs, such that:

1. every run count only decreases;
2. the state at every run boundary is unchanged;
3. the exact visited-state set is unchanged;
4. A(v)=A(w); and
5. |v| <= r^2(H+P).

Here polynomial time refers to k, r, and the binary encoding lengths of the
run counts. The algorithm need not expand w or v. Every nontrivial cycle of
f_a has length at most k; the new dead state's cycle has length one. Hence
P_a divides lcm(1,...,k) and in particular P<=k!.

Consequently, for EVERY flag relation G and Bad set on this automaton, w is a
witness if and only if v is. This is equality of full profiles, not merely
preservation for one chosen G. The empty accepted word is handled separately
and is unchanged.

## 2. A common compression of the count gaps

For each letter a separately, sort the DISTINCT positive run counts of that
letter and adjoin zero:

    0=x_0 < x_1 < ... < x_m.

For g=x_i-x_(i-1), replace it by

    g' = g,                         if g<=H;
    g' = H+1 + ((g-H-1) mod P_a),   if g>H.

Put x'_i=sum_(j=1..i) g'_j. Every occurrence of count x_i is replaced by x'_i.

### Gap lemma

For all x<=y in this finite set of counts including zero:

* x'<y' exactly when x<y;
* if y-x<=H, then y'-x'=y-x;
* if y-x>H, then y'-x'>H;
* y'-x' is congruent to y-x modulo P_a; and
* each mapped positive count is at most m(H+P_a).

Proof: every individual gap is positive, no larger than its original, and
congruent modulo P_a. A difference at most H is a sum of gaps all at most H,
so none changes. For a difference larger than H, either it contains one gap
larger than H (whose replacement still exceeds H), or all its gaps are
unchanged and their sum still exceeds H. Summing at most m gaps proves the
bound. This also proves preservation of equality and order of all counts.

It is essential to compress the gaps of a COMMON ordered list. Compressing
counts independently can turn distinct lengths into equal lengths, creating
new suffix matches. The explicit counterexample in Section 6 shows this.

## 3. One-letter orbit facts

For a function on k+1 states, every orbit is ultimately periodic. Its
nonperiodic prefix has length at most k, and its period divides P_a. Therefore
for exponents x,y that are either equal and at most H, or both exceed H and
are congruent modulo P_a,

    f_a^x(p)=f_a^y(p), for every state p.

A prefix of such an orbit has visited every state it will ever visit after
at most k+1 steps. In particular, replacing a count greater than H by another
count greater than H preserves its visited-state set. Counts at most H are
unchanged by the gap lemma applied to zero.

On ordered pairs, use f_a x f_a. Its orbit has at most (k+1)^2=H states. A
prefix of length at least H therefore contains the entire reachable pair
orbit. This finite saturation controls the set of states at matching unary
tails, even when the two run lengths are different.

For starts p,q and counts x,y>0, define

    T_a(p,q;x,y) = {(f_a^(x-t)(p), f_a^(y-t)(q)):
                    1<=t<=min(x,y)}.

Let m=min(x,y). This is exactly the first m states of the pair orbit starting
at

    (f_a^(x-m)(p), f_a^(y-m)(q)).

The common count-gap compression preserves its starting pair: the offset
|x-y| is unchanged when small and preserves both largeness and phase when
large. It also preserves the stopping set: m is either unchanged and at most
H, or both old and new m exceed H, so both traverse the full pair orbit.
Hence

    T_a(p,q;x,y)=T_a(p,q;x',y').

These facts first prove unchanged run-boundary states inductively, then
unchanged visited-state sets. Undefined transitions remain undefined via the
absorbing dead state; since the original accepted word never reaches it, the
normalized word does not either.

## 4. Exact decomposition of all agreement pairs

Let p_i be the state at the start of run i, and let l=r-1 be the final run.
The following decomposition proves the full-profile statement and is also an
exact symbolic profile algorithm.

### 4.1 Final homogeneous run is short

Its length n_l is strictly less than k. Otherwise its k+1 or more boundary
states repeat. Equal states at two positions inside an accepted run of one
letter imply that the same remaining suffix reaches the final state earlier
than the actual end. A terminal accepting state cannot then be continued.
This is a contradiction. Thus n_l<k, and compression leaves n_l unchanged.

### 4.2 Diagonal and empty-suffix comparisons

These contribute exactly

    {(q,q): q visited} union {(q,f): q visited},

where f is the accepting endpoint. Both the endpoint and visited-state set
have already been shown unchanged.

### 4.3 A target starting in a nonfinal run

Suppose a proper target suffix starts inside run j<l. It has t positive
copies of a_j before its first letter change. A matching earlier occurrence
must start in an earlier run i<j of the SAME letter, with exactly t copies
remaining in that run. Two different positions within one run cannot match a
suffix that changes letter: their first changes would occur at different
positions. Opposite-letter starts cannot match at all.

Put d=l-j. After the first equal tails, all subsequent COMPLETE target runs
except the last must match corresponding source runs exactly. For the final
run, whose end terminates the comparison, the source only needs enough letters.
Thus the guard is exactly

    n_(i+h)=n_(j+h), for 1<=h<d;
    n_(i+d)>=n_l.

It is an inequality, NOT equality, at the last run. For binary alternating
runs all the paired letters agree automatically. The state pairs contributed
when this guard holds are exactly T_(a_i)(p_i,p_j;n_i,n_j).

Compression preserves the guard: all equality comparisons are between counts
of the same letter, and the final inequality compares a mapped count with
the unchanged small n_l of the same letter. The gap lemma preserves their
order. The pair-orbit lemma preserves the entire contributed set T.

### 4.4 A target starting in the final run

This target is just a_l^t for 1<=t<=n_l<k. Its target state is
f_(a_l)^(n_l-t)(p_l), unchanged. Its source can start in any same-letter run i
with n_i>=t, at every offset x with 0<=x<=n_i-t. Thus the source-state set is

    {f_(a_l)^x(p_i): 0<=x<=n_i-t}.

If n_i<=H, the count is unchanged. If n_i>H, both old and new n_i are greater
than H. Subtracting t<k still leaves enough steps to traverse the entire unary
orbit, so the source-state set is unchanged. This includes source starts in
the last run itself and introduces no crossing of a letter change.

The four cases exhaust all pairs, proving A(v)=A(w). Summing at most r counts,
each at most r(H+P), proves the length bound.

## 5. Run-bounded existence is NP-complete (C055)

Consider the decision problem whose input is a binary terminal Instance I and
a nonnegative run bound R encoded in UNARY. Ask whether I has a witness with
at most R maximal homogeneous runs. R is a supplied bound, not a claimed
bound for an arbitrary positive instance.

### NP membership

C054 bounds every count of a suitable witness by

    R((k+1)^2+lcm(1,...,k)).

The binary encoding of a count has O(log(R+1)+k log(k+1)) bits. Guess the
starting letter, at most R positive counts, and use the exact profile algorithm
from Section 4. One-letter orbits and pair orbits have polynomial size;
whole-run guards are polynomially many equality/order tests. Large integers
are used only in arithmetic, comparisons and remainders. No loop expands a
count. Finally check acceptance, the visited-state Bad conditions, and
A(w) intersect G = empty. This is a polynomial-time certificate verifier.

The provided `solve_run_bound` uses exhaustive enumeration, not a claim of a
polynomial deterministic algorithm. Exhaustion returns NO_WITHIN_RUN_BOUND,
which must NEVER be interpreted as unrestricted nonexistence.

### NP hardness

Unary DFA intersection nonemptiness is NP-complete. A primary reference
summarizing this classical result is Fernau, Hoffmann and Wehar, *Finite
Automata Intersection Non-Emptiness: Parameterized Complexity Revisited*
(2021), https://arxiv.org/abs/2108.05244, Section 1, p.2.

Require a positive common word without loss of generality by prefixing one
unary letter to every input language. Add a universal input DFA if necessary
to have r>=2 inputs. For each input DFA, create a fresh entry and one copy of
all its states. An entry reads 1 to the state reached after one input letter;
state copies simulate 1, and input accepting copies may read 0 to the next
entry or a sole terminal final f.

Candidates are precisely

    1^n_1 0 ... 1^n_r 0, with n_i>=1 and 1^n_i in L(M_i).

For each earlier block i, flag its entry into all state copies of the final
block, and all its state copies into the final entry. As in C046, n_i<n_r
violates the first group and n_i>n_r violates the second. When all counts
are equal neither group is violated. Thus witnesses correspond exactly to
positive common unary words. Every candidate has exactly 2r maximal runs.
The construction has 1+sum_i(n_i+1) states (here n_i denotes input state
counts in this size formula), polynomially many flags, and bound R=2r.
This is a polynomial reduction. No unrestricted NP upper bound follows.

### The remaining quantifier

A computable bound R(I) on the required run count would combine with C054 to
give a full terminal decision procedure. No such general bound is proved.
C050 already excludes every POLYNOMIAL state-count bound: its unique witness
W_d has exactly

    (d+1)(d*2^d+2)

maximal runs on O(d^2) states. Indeed C_d contains d*2^(d-1) zero bits, every
encoded zero produces an isolated zero, and each encoded block has one final
00 delimiter. Each of d+1 copies starts with 1 and ends with 0, giving the
formula. Thus C054 must not be combined with a guessed polynomial R.

## 6. Concrete normalization and failed strengthening

Use the five-state transition table from C051 but remove its old flags. Let
N=10^80 and

    w=1^N 0 1^(N+1) 0.

Here H=36 and both one-letter periods are one. The common ordered count map
sends N to 37 and N+1 to 38. Therefore

    v=1^37 0 1^38 0,

has length 77 and exactly the same full agreement profile. Set G to every
state pair OUTSIDE that profile. Then both are genuine witnesses for this
maximal preserving flag relation, and the actual subtype realization of v
passes the independent canonical regular-model check.

Mapping the two long counts separately to the same representative 37 yields
1^37 0 1^37 0 instead. It creates pair (0,2), which was absent originally,
and fails the maximal-flag instance and the canonical model check. This is a
failure of independent residue compression, not a failure of the common-gap
normalization theorem. No explicit expansion of the 10^80-letter counts was
attempted or is needed.

A separate guard fixture uses the terminal path for `01101`: suffix `01`
matches the beginning of `011`. Replacing the last-run >= guard in Section 4
by equality would miss the agreement pair (0,3).

## 7. E035 reproduction and scope of the evidence

Run `python3 experiments/check_run_normalization.py` from the repository root.
The standard-library output is `results/run-normalization.json`.

The completed run records:

* all 256 partial three-state terminal tables, every accepted word through
  length seven (780 accepted words), and 1,974 accepted words from additional
  seeded tables;
* all 288 complete unary transformations on one through four states, 135,535
  exact gap-invariant checks, and 26,136 independent tail-orbit comparisons;
* 344 longer explicitly expanded words with forward/reversed/profile checks;
* 216 huge run-length encoded words, including binary-integer counts with
  25 to 89 decimal digits, checked symbolically; 331 strict compressions across
  the longer and huge samples;
* 480 complete run-bounded queries on 120 acyclic candidate languages:
  215 YES, 265 NO_WITHIN_RUN_BOUND, no unexpected cap;
* all 1,296 pairs of partial two-state unary DFAs, and 20,736 block vectors;
  the independent positive-unary product oracle has 163 positive and 1,133
  negative cases;
* two exact canonical regular-model checks, six counting-family run counts,
  three iterable/API regressions, and a deliberate cap returning UNKNOWN.

The huge-input comparisons are NOT independent expanded-word tests. Their
all-length correctness rests on the orbit and profile proofs; the expanded
finite tests cross-check those formulas independently. Generator-consumption
issues in two initially generic helper interfaces were fixed before the final
run, with explicit iterator regressions. No new conclusion was based on an
incorrect helper result. No full repository suite or Lean build is claimed.

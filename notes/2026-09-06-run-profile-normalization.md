# Exact binary normal forms and full agreement-profile run contraction

Date: 2026-09-06. Base: PR #10, `6a13dfb3bf90da83deefe3cf5749cbf6949fa052`.
Approaches: A008/A017, with implications for A012. Proposed C057-C059; E036.

**Status: written proofs and reproduced checks; independent review pending;
not Lean-checked.** Unrestricted Problem 1.7 is not solved here. Unlike the
preceding target-frontier certificate, the main run-contraction theorem has no
restriction on flag targets, marker cycles, or terminality of accepting states.
Its remaining parameter is the number of occurrences of the final letter.
No literature-priority claim is made for the coding or contraction arguments.

## 1. The full problem already has bounded data runs (C057)

Let I be any k-state partial deterministic binary BorderAvoid instance. Form
J with original boundary states q and one helper h_q for every original q.
Replace every transition p --a--> q by

    p --a--> h_q --0--> q.

Helpers have no 1 transitions. The initial state, accepting states, Bad set,
and flags are copied onto original boundary states only. Helper states are
neither accepting nor annotated. There are exactly 2k states, including any
unreachable helpers, and the same number of flags.

Define the injective uniform morphism

    C(0)=00, C(1)=10.

Every accepted run of J alternates boundary and helper states. Therefore
L(J)=C(L(I)). Its nonempty words end in 0 and contain no 11, so when split
at every 0 their intervening data blocks have lengths only zero or one.
If I's accepting states are terminal, J's accepting states are terminal too.
The graph of data-1 transitions has no directed cycle at all.

For boundary positions 2i and 2j of C(w), injectivity and equal codeword length
imply

    C(w)[2j:] prefix-of C(w)[2i:] iff w[j:] prefix-of w[i:].

Both endpoints of every flag are boundary states; no odd-position comparison
is flagged. Empty-suffix and diagonal cases are included. Original state
visits and their Bad checks are exactly the visits at even positions. Hence

    Witness_J(C(w)) iff Witness_I(w),
    A_J(C(w)) intersect (Q x Q) = A_I(w),

where A is the full state-pair agreement profile. The second statement is a
projection identity, NOT equality of the larger raw profile: J has extra
helper-state agreement pairs, but they have no flags.

**Consequence.** Deciding binary terminal BorderAvoid even on this restricted
class with data runs of length at most one suffices to decide every binary
terminal instance. Recurrent marker/target configurations are not merely a
small residual avoided by choosing simple data blocks; this normal form still
contains the entire problem. This is an exact reduction, not a solution.

Unlike the previously refuted operation of appending a fresh terminal marker,
C recodes EVERY symbol in BOTH compared occurrences. For the flagged path 00,
the output 0000 is still invalid: the original forbidden comparison simply
moves from positions (0,1) to (0,2). No required agreement is destroyed.

### Last-letter slicing without adding states

For a terminal instance, fix an original final f and a bit b. Retain f as the
only final and delete only transitions into f labelled with the other bit.
No earlier accepted-run transition is lost because an original final is
terminal. For nonempty words, the resulting language is exactly the words of
the original instance ending at f with last bit b. Flags, state IDs, and Bad
are unchanged. The union over all (f,b), together with a separately checked
empty word, is exact for witness existence.

For b=1, globally exchanging 0 and 1 gives the unary-data / zero-marker format.
This removes 'accepted word ends in the wrong symbol' as an obstruction to the
previous solver. It does not remove marker cycles reachable from targets.
The supplied `final_symbol_frontier_decision` runs C056 on all these exact
slices. NO requires every slice to be completely decided NO. Any unresolved
slice prevents a global NO; any independently checked YES is sufficient.

This slicing lemma requires terminal acceptance. C057's uniform morphism and
C058 below also work with nonterminal acceptance.

## 2. Exact state-pair profile of a run-length vector

For any nonempty binary accepted word w, let b be its final letter and a the
other letter. Write the UNIQUE decomposition

    w = a^n_0 b a^n_1 b ... a^n_(r-1) b,   n_i >= 0.

Here r is the number of occurrences of b, not the number of maximal runs of
either symbol. Zero-length data blocks are retained, so adjacent b's each
have a separate block. No new separator or symbol is introduced.

Let p_i be the state at the start of data block i, and f the final endpoint.
Write F(q)=delta(q,a). Complete this unary function with an absorbing undefined
state sink. The completed state set has s=k+1 elements. Put

    h=s, T=s^2,
    P=lcm(lengths of all cycles of F).

The absorbing sink contributes cycle length one. Other cycles use original
states; hence P divides Lambda_k=lcm(1,...,k). A unary run is on its eventual
cycle by time h. For any q and exponents x,y>=h with x=y modulo P,

    F^x(q)=F^y(q).

The set of visited unary states has stabilized by time h. These facts follow
by the pigeonhole principle on a deterministic functional graph.

For two data runs define the exact aligned-tail pair set

    H(p,n;q,m) = { (F^(n-t)(p),F^(m-t)(q)) : 0<=t<=min(n,m) }.

Do not confuse H with flags: H records EVERY state pair at an equal data-tail
length. Unary data tails of a given length are always identical.

For i<j define the later-block guard

    R_ij := AND_{z=1,...,r-1-j} [n_(i+z)=n_(j+z)].

The whole agreement profile is exactly the union of:

1. (q,q) for every visited state q;
2. (q,f) for every visited state q (empty-suffix agreements);
3. H(p_i,n_i;p_j,n_j) for every i<j for which R_ij holds.

**Proof.** A nonempty target suffix reaches its first b after t a's. A matching
source must reach its first b after exactly t a's too, since a differs from b.
For distinct positions in the SAME block this cannot happen. For different
blocks it gives the equal-tail pair above. The remainder of the target suffix
consists of whole blocks ending in b, which must match exactly the subsequent
source blocks. This is precisely R_ij. Conversely these equalities concatenate
to the desired suffix-prefix agreement. The source factor need not end at the
end of the whole word; it ends at the corresponding earlier marker. This
argument does not assume accepting states are terminal and includes t=0,
empty data blocks, recurrent targets, and arbitrary proper overlaps.

## 3. A finite numerical signature for all tail pairs

For fixed p,q, H(p,n;q,m) is completely determined by:

* the sign of n-m;
* if |n-m|<h, that exact difference; otherwise its residue modulo P;
* if min(n,m)<T, that exact minimum; otherwise just the fact min(n,m)>=T.

For n>=m set d=n-m and rewrite H as the states visited in the pair orbit

    (F^d(p),q), (F^(d+1)(p),F(q)), ..., (F^(d+m)(p),F^m(q)).

The initial pair depends on d exactly below h and only on its residue modulo
P above h. The deterministic pair orbit has at most s^2=T states. A prefix of
m+1 states with m>=T has already seen every state that can ever occur; later
iterations add none. For m<T retain its exact value. The case n<m is symmetric,
with the longer-run shift applied to q instead. This proves the signature claim.

The threshold T is conservative. No claim of optimality is made. The algorithm
stops a pair orbit on its first repeated pair rather than expanding large n,m.

### A necessary guard: order and residues alone are insufficient

Take the six-state terminal table (columns 0,1)

    ((-1,1),(-1,2),(3,2),(-1,4),(5,4),(-1,-1)),

start 0, final 5, and flag (1,3). Its data-1 period is one. The words with run
lengths (101,100) and (102,100) have the same weak order, the same residues,
and all lengths greater than T=49. The first is invalid and the second valid.
At difference one, the aligned pair at the second block's entry is (1,3);
at difference two it is (2,3). The other relevant pairs do not restore (1,3).
Thus forgetting short differences would make the proposed abstraction unsound.
This counterexample is retained as a regression.

## 4. Global profile-preserving contraction (C058)

For a supplied finite vector n=(n_0,...,n_(r-1)), construct a strictly increasing
map phi on its distinct length values as follows. Every value at most T is
fixed. Treat T itself as an additional anchor even when absent from the vector.
Sort the distinct values greater than T. If consecutive old values (starting
with T) differ by g, choose their new difference

    g' = g                       if g<h,
         h+((g-h) mod P)          if g>=h.

Set n'_i=phi(n_i). Every g' is positive, at most g, and congruent to g modulo P.
Thus phi is injective and increasing, phi(x)<=x, and phi(x)=x modulo P.
Values above T remain above T. Values at most T remain exact.

For ANY two distinct original length values, a difference smaller than h is
preserved exactly: all intervening sorted gaps are smaller than h, and each
was left unchanged. A difference at least h remains at least h. Indeed either
it contains a gap at least h, whose contraction is still at least h, or it is
a sum entirely of unchanged small gaps. In both cases its residue is preserved.
Therefore every pair signature in Section 3 is unchanged.

Data-run endpoints are also preserved: lengths below the threshold are exact;
large lengths stay beyond the unary transient and retain their residues. Since
marker transitions are unchanged, induction preserves every block-start state
p_i and the overall endpoint f. Every data-run visited-state set is preserved
as well, either exactly or by saturation beyond the transient. In particular
an undefined run cannot be converted into a defined accepted run, or vice versa.

Equality of block lengths is preserved by injectivity, so every R_ij remains
unchanged. Section 3 preserves every H pair set. Section 2 now gives

    A(a^n'_0 b ... a^n'_(r-1) b) = A(w),
    Visited(new_word) = Visited(w),
    Endpoint(new_word) = Endpoint(w).

**Theorem C058.** For EVERY partial deterministic binary DFA and EVERY accepted
word, this computable contraction preserves its full state-pair agreement
profile, visited states, and endpoint. It never increases length. Consequently
it preserves witnesshood for EVERY flag relation and Bad set on that same DFA.
The transformation is independent of G and Bad. It may leave a word unchanged.
It is not a claim that every long witness can be strictly shortened.

### Bound and algorithmic size

If d is the number of distinct run lengths, every contracted value is at most

    T+d(h+P-1) = (k+1)^2+d(k+P).

There are at most d contracted gaps above T, and each is at most h+P-1; this
proves the bound. Since d<=r, the new total word length is at most

    r[(k+1)^2+d(k+P)+1]
      <= r[(k+1)^2+r(k+Lambda_k)+1].                    (1)

The function on the right is polynomial in r for fixed k, with the explicitly
computable unary-period factor Lambda_k. The normalization on binary-encoded
integer lengths does not expand their letters. Endpoint and profile evaluation
uses finite unary/product orbits, even for supplied integers of size 10^30.
A huge-integer computation is not reported as direct expanded-word enumeration.

For r=0 the only word is epsilon and it is left unchanged. k>=1 throughout.
This proves neither the old k-2 budget conjecture nor strict profile descent:
the NUMBER r of final-letter occurrences is not bounded by this argument.

### A recurrent-target example

Take

    delta=((1,0),(2,1),(3,0),(-1,-1)), final={3}, G={(0,1)}.

The target 1 lies in a productive cycle containing 0-marker transitions. C056's
unary certificate is NOT_APPLICABLE. The witness with data-1 lengths

    (401,307,401,307,0)

has length 1,421. C058 contracts it to

    (35,30,35,30,0),

length 135, with EXACTLY the same profile. Both direct word predicates check it.
This is a normalization beyond C056's hypothesis, not a complete decision of
all inputs failing that certificate. The generic wrapper still returns UNKNOWN
on this example; the displayed positive word was supplied and independently
checked.

## 5. The remaining marker-count problem is exact, not a heuristic (C059)

For a nonempty word w define mu(w) as the number of occurrences of its last
letter; let mu(epsilon)=0. For a positive instance, minimize over its witnesses.

For any fixed marker budget r, (1) gives a finite COMPLETE witness search for
all words with mu<=r, regardless of marker cycles or recurrent targets. One
may enumerate binary words through the displayed bound, retaining mu<=r, or
enumerate run vectors through the contracted bound. It is not legitimate to
interpret failure under a supplied r as an unrestricted NO. The experiment
code implements normalization/profile checking, not a claimed efficient
implementation of this enormous finite enumeration.

A computable uniform bound M(k) on the minimum required mu for positive
terminal k-state instances would give an unrestricted word-length bound

    L(k)=M(k)[(k+1)^2+M(k)(k+Lambda_k)+1].

Enumerating through L(k) would decide terminal BorderAvoid. Conversely an
unrestricted decider gives a computable M(k): enumerate the finitely many
k-state encodings, decide each, and enumerate words to obtain one witness
for each positive case. Take the maximum mu of the resulting finite list.
Thus such a computable marker-count bound exists iff the terminal existence
problem is decidable. Through C030/C031 and the prior forward bridge this
retains the repository's route to the normalized subtype problem, at the
recorded proof status of those reductions.

C057 sharpens the scope caution. Even if attention is restricted to outputs
with no consecutive ones and all nonempty words ending in zero, bounding
marker counts is already enough to settle every original instance: every
letter of an original witness contributes at least one zero to its encoding.
So the unresolved block-count problem retains the full difficulty of the
original problem. C058 does not turn it into a demonstrably easier problem.

### Polynomial marker bounds are already false in the bounded-run normal form

Use C046's modular family with r blocks and periods p_i. Its exact witnesses
are (1^N0)^r for positive multiples N of P0=lcm(p_i). C057 transforms them into

    ((10)^N 00)^r.

All data-1 blocks now have length at most one. The exact minimum number of
zero markers is r(P0+2); the shortest encoded word has length 2r(P0+1).
The original k states become 2k; the flag count is unchanged. These identities
follow from the word-preserving reduction and C046's all-length language, not
from an additional high-budget search.

Taking r=m and periods 1,...,m gives 2k=(m+1)(m+2) and at least 2^(m-1)
markers, by C046's elementary LCM lower bound. No polynomial marker-count
bound exists, even in this very simple data-run normal form. This is not a
noncomputability result. It also explains why the contraction cannot be
unconditionally strict: the already-small zero/one run lengths do not change.

## 6. Other attempted transfers and limitations

We checked the potential connection with Michaliszyn, Otop and Wieczorek,
*Reachability and Bounded Emptiness Problems of Constraint Automata with Prefix,
Suffix and Infix* (CONCUR 2023),
https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2023.3.
Its stated finite reachability theorem concerns constraints between consecutive
tuples of words. The arbitrary-distance block guards R_ij above have NOT been
reduced to that setting with a bounded number of registers. No decidability
transfer or new impossibility result is inferred from that source. The exact
profile identity is self-contained and does not depend on it.

A residue-only abstraction was tested and rejected by the explicit short-gap
counterexample in Section 3. Independently capping each run also risks merging
previously unequal lengths and changing the later-block guards. The proved
map instead preserves their full weak order and all transient-sized gaps.

The general statement proved here is normalization CONDITIONAL ON r, not an
unrestricted marker-count bound. A finite signature for two run lengths is
not a finite-state summary of arbitrarily long sequences of run lengths.
The guards can compare unbounded sequences of subsequent blocks. That is
exactly the information still missing from a terminating general solver.

## 7. Reproduction (E036)

Run `python3 experiments/check_run_profiles.py`. The standard-library suite
records the following checks with seed 2026090657:

* all 75 partial unary maps on one, two, and three states, including absorbing
  undefined behavior: 7,576 state-orbit checks and 448,386 exact tail-pair sets;
* 6,753 defined words for every two-state binary transition table, with both
  direct profile formulations; 6,809 numeric/raw profile comparisons overall;
* 137 long accepted candidates, all strictly contracted, removing 99,242
  letters; 548 additional random flag/Bad preservation checks;
* 640 vectors of large binary-encoded integers (around 10^30), including
  20,228 pair-signature and exact orbit-set preservation checks;
* 200 arbitrary terminal instances and 50,800 word checks for exact last-bit
  slicing; 160 complete acyclic oracles for its solver wrapper (105 YES/55 NO);
* 20,320 encoding/witness comparisons, 81,760 raw encoded-language checks,
  12 bounded-run instances from C051's family, and four exact canonical
  regular-model path checks for the coding transformation;
* explicit guards for lost short-gap information, unresolved recurrent
  targets, and the former wrong-final-symbol rejection.

Finite tests support the implementation. They are not an independent
mathematical review of the quantified proofs. The paired tail-orbit oracle
iterates states directly rather than calling the compressed algorithm; the
raw-profile oracle enumerates all position pairs. Large integer cases are
not expanded into strings.

No full repository CI or Lean build is claimed. The original core regression
and E035 are rerun separately before integration; final replay results are
recorded in the commit and PR rather than assumed here.

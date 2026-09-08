# Necessary-budget incompleteness and exact delimited convolution

Date: 2026-09-06. Base: PR #8, `c73f5af1240ae7b1f019cf9df3130791c93b8422`.
Approaches A012/A017. Proposed C051-C053; experiments E033/E034.

**Status: written proofs with reproducible finite checks; independent review
requested; not Lean-checked.** This work does not decide unrestricted Problem
1.7. It proves that one general NO-search strategy is incomplete, then gives
an exact finite-state replacement for a precisely specified class. No priority
claim is made. Original arbitrary, possibly infinite tree semantics are retained.

## 1. A five-state NO instance defeats every finite necessary budget (C051)

Use start 0, sole accepting state 4, no Bad states, and

    G = {(0,2), (0,3), (1,2)}.

The binary partial transition table is:

| State | 0 | 1 |
|---|---|---|
| 0 | 2 | 1 |
| 1 | 2 | 1 |
| 2 | undefined | 3 |
| 3 | 4 | 3 |
| 4 | undefined | undefined |

All states are reachable and co-reachable to acceptance. State 4 is terminal.
Both cyclic components are one-state unary loops. Thus the candidate graph
is flat in the sense of C033, not an example requiring nonflatness.

### Its entire witness language is empty

The accepted words are precisely

    1^n 0 1^m 0, with n>=0 and m>=1.

For every such word one of three cases applies.

* If n<m, compare the initial suffix, starting in state 0, with the suffix
  beginning inside the second block exactly n ones before the last zero.
  The latter starts in state 3 and equals `1^n0`, a prefix of the whole word.
  This violates (0,3). The argument includes n=0.
* If n=m, the suffix at the second-block entry, in state 2, is `1^n0` and
  matches the initial prefix. This violates (0,2).
* If n>m, start inside the first block exactly m ones before its zero.
  That state is 1. The second-block suffix is `1^m0` and matches there,
  violating (1,2).

Hence no accepted word is a witness. This is an all-length case analysis.

### Nevertheless every necessary language is nonempty

For n>=0 put

    w_n = 1^n 0 1^(n+1) 0.

The length is 2n+3. There is exactly one violating position pair:

    (i,j) = (0,n+2),
    suffix length = n+1,
    gap = n+2.

Indeed the first target block is longer by exactly one, so (0,3) matches at
that unique equal-tail position. Flag (0,2) would require n=n+1 and (1,2)
would require the first block to be longer. No diagonal or empty-suffix flag
is present, and state 0 is visited only initially.

The necessary predicate checks this pair if the suffix length is at most L
OR its gap is at most D. Therefore, for all nonnegative L,D,n,

    Necessary(I,w_n,L,D) iff n+1>L and n+2>D.

In particular

    for every L,D: Necessary_I(L,D) is nonempty,
    but Witness_I is empty.

Increasing L and D never produces an empty necessary automaton for this fixed
instance. This refutes completeness of the general NO semiprocedure that waits
for such an emptiness certificate, even with no state cap and fair enumeration
of all budgets. It does not refute the soundness of any individual necessary
emptiness certificate, or the positive sufficient-budget semiprocedure.
The pointwise identity between Witness and the intersection of all necessary
languages is compatible with this result: the word surviving the test depends
on the budget. Interchanging these quantifiers would be incorrect.

C030 gives an always-satisfiable normalized bottom/product realization with
11 variables and 13 constraints. Its query is entailed, but none of the
corresponding fixed necessary-budget graphs proves that by emptiness.
The transfer retains C030's written/audited status. No smaller-state minimality
claim is made here.

The example was first found through a longer encoded construction and then
reduced to this direct five-state table. The retained theorem and regression
use the smaller table, not an unverified minimization inference.

## 2. Exact arbitrary-flag decisions for bounded delimited schemas (C052)

Fix r>=1 partial binary data DFAs M_i with n_i states, starts s_i, and accepting
sets F_i. Use disjoint logical stage states (i,q), with 0<=i<r, and a terminal
state f. A candidate word has the logical form

    u_0 # u_1 # ... u_(r-1) #,  u_i in L(M_i),

where the single shared marker # is not a data symbol. The number of stages
is finite and supplied, but each data word is unbounded and its DFA may have
arbitrary nonflat recurrent components. An arbitrary Bad set and arbitrary
ordered flag relation may be specified on all logical states and f.

To stay within binary BorderAvoid, encode

    E(0)=10, E(1)=11, E(#)=00.

For each logical state add a data-token helper; add one separator helper per
stage and a terminal f. This uses 2*sum(n_i)+r+1 binary states. Only logical
boundary states and f carry flags/Bad; helpers do not. This annotation scope
is explicit. The theorem is not a claim about arbitrary flags inside tokens.

### Mandatory boundary exclusions

No word can visit a Bad state, a diagonally flagged state, or a state with a
flag into f, because the empty suffix agrees everywhere. Apply these exclusions
within each stage. Reject a bad or diagonally flagged f. Flags sourced at f
cannot be used in a strict ordered pair; flags directed from a later stage
to an earlier stage cannot be used either.

### The exact cross-stage formula

Let c_i(t) be the stage state immediately before the last t data letters of
u_i, for 0<=t<=|u_i|. In particular c_i(0) is its data accepting endpoint.
For i<j define the whole-block context guard

    R_ij := AND_{h=1,...,r-1-j} [u_(i+h)=u_(j+h)].

The empty conjunction, when j=r-1, is true. A proper flagged agreement with
source in stage i and target in stage j exists exactly when R_ij holds and
there is a depth t with

    0<=t<=min(|u_i|,|u_j|),
    suffix_t(u_i)=suffix_t(u_j),
    G((i,c_i(t)),(j,c_j(t))).

Proof: each target suffix reaches a first marker. A matching earlier occurrence
must reach its first marker at the same offset, so the data tails have equal
length and content. Every subsequent complete target block must match the
corresponding complete source block, giving precisely R_ij. Conversely those
equalities concatenate to the required suffix-prefix match. For two distinct
cuts in the SAME stage, the first marker would occur after different numbers
of data letters, so no proper agreement is possible. For binary expansion,
both flagged endpoints are aligned token boundaries; data tokens begin with
1 while a marker is 00, so the same argument applies. Accidental occurrences
of 00 at an unaligned bit offset have no flagged endpoint.

This formula includes t=0, targets in every stage (not just the last), empty
data words, arbitrary DFA cycles, and all ordered flags. Its implementation
`block_witness` is independent of the finite convolution search below.

### A finite reverse padded-convolution machine

Read every u_i backwards, simultaneously, padding a completed word with a
fresh padding symbol. The finite memory contains:

1. the current reverse DFA state q_i for each stage, or FINISHED;
2. one equality bit e_ij for each i<j, saying that all columns read so far
   in the two reversed/padded data words are equal;
3. one hit bit h_ij, saying that an equal-tail depth with a flagged state pair
   has occurred while both words were still active.

Start nondeterministically in safe accepting states of the stage DFAs. All e
bits start true and hit bits are observed immediately, accounting for empty
data tails. A reverse step chooses a predecessor on a data letter. A stage
may instead finish only at its own start state, after which it emits padding
forever. Unequal symbols (including data versus padding) clear the e bit
permanently. A flagged pair at an equal active depth sets h permanently.

Crucially, a hit MUST NOT be rejected merely when first seen, except if its
context guard is already unconditionally true. When all coordinates finish,
e_ij means equality of the WHOLE data words, including length. At that point
accept exactly when

    for every i<j: h_ij implies NOT R_ij,

with R_ij evaluated from the final e bits of the later block pairs.
A hit at an earlier equal tail must be retained even if that pair's e bit later
becomes false: the earlier tail agreement still exists. The guard concerns
other, subsequent whole blocks.

Every finite successful machine path supplies data words and complete valid
reverse runs, and the cross-stage formula proves witnesshood. Conversely every
witness tuple supplies such a path, and its final guard tests accept. This is
a sound and complete finite construction for the supplied schema.

### Why delayed context guards matter

Take three one-state universal data DFAs and only the flag from stage 0 to
stage 1. The empty tails always produce h_01. But R_01 is the equality of
blocks 1 and 2. Thus blocks (epsilon,0,1) give a witness, whereas
(epsilon,0,0) do not. Rejecting the hit without waiting for the whole-block
equality would give a false negative. This is a regression fixture.

### State, witness, and space bounds

Put b=binom(r,2) and P=product_i(n_i+1), including FINISHED for each coordinate.
There are at most

    P * 2^(2b)

machine states. This alone proves termination without practical caps.

A sharper successful-path bound follows from monotonicity: e loses at most
b bits and h gains at most b bits. There are at most 2b+1 mask phases. In a
shortest accepting path, no coordinate tuple repeats inside a mask phase,
since that would repeat the entire memory state. Hence a positive schema has
an accepting convolution of length at most

    H=(2b+1)P.

Each coordinate uses at least one finishing/padding column, so the binary
witness length is at most 2rH. This is a bound for THIS schema, not unrestricted
Problem 1.7. The BFS minimizes convolution length, not total witness length.

A machine state uses polynomially many bits in the supplied schema size.
One can guess an initial state and transitions and search for an accepting
path using a binary counter through the finite state bound. Thus the exact
schema existence problem is in PSPACE. C048 embeds DFA intersection: its
predecessor tags are simply incorporated into the stage DFA states, and its
special flags are a permitted input relation here. Therefore the class is
PSPACE-complete. The classical source fact is DFA-intersection PSPACE
completeness, for which a primary reference is Fernau, Hoffmann and Wehar,
*Finite Automata Intersection Non-Emptiness: Parameterized Complexity
Revisited* (2021), https://arxiv.org/abs/2108.05244.
No unrestricted PSPACE upper bound is implied.

## 3. Automatically certify a class of raw inputs (C053)

The preceding solver need not always require a manually supplied decomposition.
`marker_certificate.py` accepts a raw binary terminal Instance and derives a
complete schema cover when one of two checkable formats applies. No marker is
inserted into the input language.

First choose a final f and remove Bad states, diagonals, and all sources of
flags into f. Restrict to reachable/co-reachable states. Empty slices are
settled directly; an accepting initial terminal gives the empty witness.
For the remaining slice, try either of these certificates:

* Paired format: every safe accepted word parses into data tokens 10/11 and
  marker 00, ends with a marker, and no relevant flag endpoint can occur at an
  odd token position. A product with a five-state parser verifies the language
  inclusion and parity condition. A relevant flag has both endpoints in the
  live slice and does not start at f; any endpoint reachable at an odd token
  position causes this conservative certificate to be refused.
* Unary format: data is the single symbol 1 and the marker is 0. Every safe
  accepted word must end in 0. Here every raw position is a logical boundary,
  so there is no odd-position restriction.

Construct macro transitions for the data tokens and marker. In paired mode
these are two-step raw paths; in unary mode data 0 is undefined, data 1 is the
raw 1 edge and the marker is the raw 0 edge. Retain productive macro states.
Require that NO productive macro cycle contain a marker edge. This is tested
by checking whether the target of a marker edge can reach its source.
Failure of either applicable-format test returns NOT_APPLICABLE/UNKNOWN,
not an entailment verdict.

### Finite complete cover

Every marker edge then advances strictly in the condensation DAG of the macro
graph. A macro graph with K states permits at most K-1 markers on an accepting
path. Enumerate the finitely many possible marker-edge sequences, allowing
arbitrary data-only paths between successive marker edges. Each sequence gives
a schema: stage starts and data accepting endpoints are the corresponding
marker-edge targets and sources. The stage DFA is the data-only macro graph
with these chosen endpoints.

Copy original flags to every ordered pair of stage copies having those
underlying original states. Repeated original states in different stages are
NOT identified. The original run is reconstructed exactly. The format and
annotation certificate ensures that this copying preserves every relevant
raw suffix comparison. No additional comparison is introduced by adding a
new marker: all markers already occur in the original word.

Every original safe accepted word has one of the enumerated marker-edge
sequences. Conversely every candidate in a schema has exactly the original
raw run and endpoint. Therefore the cover is complete for candidates and
preserves witnesshood. Apply C052 to every schema. A positive answer is checked
against both raw word predicates; NO is returned only after all schemas in all
nonempty final slices are certified and empty. Missing formats, a marker
cycle, or any search/cover cap leaves UNKNOWN. A marker-count bound is proved,
not supplied as an arbitrary cutoff.

For a k-state raw input, K<=k, r<=k-1, and the implementation's stage DFAs can
be represented using at most k states each. A coarse positive-witness bound
on this certified class, for k>=2, is

    2*k^3*(k+1)^k.

The class is in PSPACE by polynomial-space schema guessing and convolution
reachability; it is PSPACE-hard through the C048 images, all of which satisfy
the paired certificate. These are complexity claims for a checkable restricted
class, not the unrestricted target.

The direct five-state C051 instance satisfies the UNARY certificate. Its two
possible first-marker sources produce two schemas, both empty. The front end
therefore proves this raw input NO even though every finite Necessary(L,D)
language is nonempty. The paired-format variant of the same inequality idea
is also checked separately; its larger state count is not confused with five.

## 4. The unrestricted gap remains explicit

The format assumptions cannot be imposed by freely appending a separator.
For example, take a three-state terminal path accepting only `00` and flag
(0,1). Its only candidate is not a witness. Treating those two zeros as data
and appending the encoded delimiter gives `101000`, which is a witness in the
single-stage encoded schema: the new delimiter prevents the original internal
suffix agreement. This is a concrete failure of that proposed general reduction.

The automatic certificate does not cover arbitrary inputs with markers inside
productive cycles, significant flags at unaligned code positions, or accepted
words outside the supported formats. Delimiter alignment is exactly what
turns infinitely many possible offsets into synchronous tail depths. No proof
here eliminates arbitrary offsets in the unrestricted problem.

The existential theory of regular-constrained word equations is not by itself
a solution to the remaining universal substring obligations. For perspective,
Ganesh et al., *(Un)Decidability Results for Word Equations with Length and
Regular Expression Constraints* (2013), https://arxiv.org/abs/1306.6054, prove
undecidability of a more general positive forall-exists word-equation fragment.
That result is neither an undecidability reduction to our special problem nor
a reason to stop: it identifies why a quantifier-elimination shortcut would
need its own exact hypotheses and proof.

## 5. Executed evidence and limitations

E033, `python3 experiments/check_delimited_blocks.py`:

* 350 acyclic schema instances with complete finite-language oracles:
  126 YES, 224 NO; 482 full candidate tuples.
* 120 denser finite dictionary instances with 9,061 fully enumerated tuples;
  all 120 happened to be positive. This is not presented as a balanced census.
* 180 cyclic schema instances: 49 YES, 131 NO; 30,866 short tuples compare
  the all-cuts formula with both binary predicates. Their short-word checks
  alone are not negative certificates; the exact machine theorem is separate.
* 4,096 equality schemas from every pair of total two-state DFAs agree with
  the independent C048 product solver: 1,858 YES and 2,238 NO.
* In total 40,634 formula/binary comparisons and 18 exact canonical-model checks,
  plus 4 additional canonical checks for C051. Three explicit semantic guards
  and one intentional state cap are retained.
* C051 additionally checks 100 exponent pairs, the unique violation for
  n=0..15, 3,600 direct necessary predicates, and nonemptiness of all 25 finite
  necessary graphs with L,D<=4. The proof, not these samples, covers all budgets.

E034, `python3 experiments/check_marker_certificate.py`:

* 400 acyclic raw macro-expansion instances, with every one of their 918
  candidates enumerated independently: 211 YES, 189 NO.
* 160 cyclic compiled schemas agree with C052: 84 YES, 76 NO.
* 120 C048 constructions agree with its independent product solver:
  36 YES, 84 NO.
* Four unsupported-format guards and one intentional cap return UNKNOWN.
  Variable marker counts, multiple schemas, empty words, nonflat data SCCs,
  and the unencoded five-state NO instance have explicit fixtures.

All these runs completed without an unintentional cap or mismatch. Full source
and compact JSON outputs are committed. They are finite implementation checks;
new all-length and completeness claims rest on the written proofs above, not
on counting successful tests. The original core border regression also reproduces
its previous output byte-for-byte (Git blob aa6d1680b5442493744c667024d2df77a1bd8e78).
No Lean build, full repository-wide suite, or independent review is claimed.

## 6. Revised research target

A complete general NO procedure cannot rely solely on fixed necessary-budget
emptiness. A finite regular shared-word representation does work for arbitrary
annotations once the cross-stage alignment is controlled, and C053 supplies
an automatic complete cover for a checkable nonflat class. The outstanding
step is an alignment/decomposition theorem or different symbolic method for
raw terminal inputs outside that class. In particular, markers may not be
inserted without an agreement-preservation proof, and a bounded number of
marker occurrences may not be assumed where the productive graph has marker
cycles. Nothing here promotes these remaining obligations to established facts.

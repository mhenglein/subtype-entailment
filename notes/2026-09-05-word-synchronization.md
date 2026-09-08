# Whole-word synchronization, a PSPACE lower bound, and large skeletons

Date: 2026-09-05. Base: PR #6, commit `256b28776763457cce9574a0bad8fea1d0b258ed`.
Approaches: A011, A016, A017. Proposed claims C048-C050; experiment E032.

**Status: written proofs plus reproduced finite tests; independent review
requested; not Lean-checked.** No unrestricted decision or PSPACE upper bound
for Problem 1.7 is asserted. This continuation concerns actual binary terminal
instances and keeps arbitrary, possibly infinite type-tree semantics.

## 1. Whole words, not only unary lengths (C048)

Let M_1,...,M_r, r>=2, be partial deterministic automata over {0,1}.
Write Q_i for their disjoint state sets, q_i for their starts, F_i for their
final sets, n_i=|Q_i|, and S=sum_i n_i. Input accepting states need not be
terminal. Let

    E(0)=10, E(1)=11, and delimiter=00.

There is an effectively constructed binary terminal-final BorderAvoid
instance I with

    Witness(I) = { (E(u)00)^r : u in intersection_i L(M_i) }.

The construction has exactly 3S+2r+1 states before optional trimming, no Bad
states, no diagonal or final-column flags, and polynomially many flags.
The encoding is explicit: unlike C030, this construction does change the
input common word. No claim of preserving its intrinsic word budget is made.

### States and transitions

For stage i introduce:

* one entry e_i with predecessor tag START;
* boundary states b_(i,q,a), q in Q_i, a in {0,1}, with predecessor tag a;
* data helpers h_(i,q), q in Q_i;
* one separator helper z_i.

Add one final state f, with no outgoing transitions. Start at e_1.
The underlying DFA state of e_i is q_i; that of b_(i,q,a) is q.
From a boundary of underlying state q:

    read 1 -> h_(i,q);
    read 0 -> z_i, only if q belongs to F_i.

From h_(i,q), reading a goes to b_(i,delta_i(q,a),a), when that transition
is defined. From z_i, only 0 is defined; it leads to e_(i+1), or f for i=r.
All unspecified transitions are undefined.

The accepted candidate language is exactly

    E(u_1)00 E(u_2)00 ... E(u_r)00, with u_i in L(M_i).

The input word may be empty: an accepting input start permits the separator
immediately. Tag START is used only at that stage's entry, not at subsequent
visits to its underlying input start state.

For each i<r, flag a pair from a boundary in stage i to a boundary in stage r
exactly when their predecessor tags differ. No helper or f is in a flag.
There are

    sum_(i<r) (2 n_i n_r + 2 n_i + 2 n_r)

flags, hence the construction is polynomial in the explicit input size.

### Proof of synchronization: the rightmost mismatch

First suppose u_i differs from u_r. Let x be their longest common suffix.
Immediately before the two occurrences of x, the predecessor tags differ:
either both predecessors are bits and are unequal, or one word has already
reached its entry and has tag START while the other has a preceding bit.
They cannot both have tag START unless the words are equal.

Let p and q be those boundary positions in stages i and r. The suffix at q
is E(x)00. This is a prefix of the suffix at p, since stage i also ends with
x followed by its delimiter. The unequal predecessor tags make (p,q) flagged.
Thus unequal words cannot occur in a witness. This covers x=epsilon, empty
input words, and the case that one entire input word is a proper suffix of
the other.

Conversely, assume every u_i equals u. Consider any potentially flagged pair.
Both endpoints are code boundaries, in stages i and r. From the later boundary
the suffix has the form E(x)00. At aligned two-bit boundaries a data token
always begins with 1, while the delimiter is 00. Therefore a match from the
earlier boundary must finish at that stage's first delimiter, and injectivity
of E forces the remaining data suffixes to be exactly equal. In two copies
of the same u, equal remaining lengths select the same data boundary. Their
predecessor tags are consequently equal, including START at the entry. The
pair is not flagged, a contradiction. No other flags or boundary exclusions
exist, so the word is a witness.

This proof does not require that arbitrary binary occurrences be aligned.
Only flagged occurrences need alignment, and every flag endpoint is a token
boundary by construction. Helpers have no flags. In particular incidental
`00` across bit positions does not invalidate the argument.

### An exact nonflat subclass

With the supplied input-automaton decomposition, witness existence is exactly
DFA intersection nonemptiness. Explore the product of the input state sets;
accept a tuple when all coordinates are accepting. There are at most

    P = product_i n_i

tuples. If a common word exists, a shortest one has length at most P-1.
It produces a shortest witness of I of length at most 2rP. If the product
is exhausted without acceptance, I has no witness of any length.

`solve_sync` implements this search on demand. A state cap gives UNKNOWN.
Its output is applicable to instances produced from the supplied decomposition,
not to arbitrary BorderAvoid inputs, and every returned binary witness is
checked by both existing word predicates. The state bound is a product bound,
not a polynomial stopping rule.

This class is genuinely nonflat: even a one-state input DFA with two data
self-loops gives a productive compiled SCC with two internal labelled choices.
For two such universal inputs the witness language is exactly
`{E(u)00E(u)00 : u in {0,1}*}`. It permits arbitrarily complicated common words,
yet its existence problem is decided by the finite product.

The old C046 least-common-multiple mechanism is the unary-length special case
of synchronizing regular data. This new binary compiler does not reproduce
C046's original state or budget constants.

## 2. Complexity consequence for the exact signature (C049)

DFA intersection nonemptiness, with an input list of DFAs, is PSPACE-complete.
A primary-source statement appears in Fernau, Hoffmann, and Wehar (2021),
*Finite Automata Intersection Non-Emptiness: Parameterized Complexity Revisited*,
[arXiv:2108.05244](https://arxiv.org/abs/2108.05244). The classical source is
Kozen (1977), *Lower bounds for natural proof systems*,
[publication record](https://research.ibm.com/publications/lower-bounds-for-natural-proof-systems).
This work makes no priority claim for that theorem or for subtype hardness.

The source problem may be assumed binary: encode each letter of an input
alphabet by a fixed-length binary code, and replace each DFA edge by a finite
prefix decoder. The blowup is polynomial and common-word existence is
preserved, including empty words. A trivial universal automaton can be added
to arrange r>=2.

C048 is a polynomial many-one reduction from this binary problem to terminal
BorderAvoid existence. Thus **binary terminal BorderAvoid is PSPACE-hard**.
The construction-described synchronization subclass is PSPACE-complete when
its supplied DFA decomposition is part of the input: its membership follows
from the original intersection problem. No automatic decomposition algorithm
for arbitrary annotated automata is asserted.

Apply C030 to the compiled k-state instance. It produces an always-satisfiable
normalized constraint system over only bottom and one covariant binary product,
on 2k+1 variables, with the same separating binary paths. It follows that
**non-entailment for this exact normalized signature is PSPACE-hard, even on
satisfiable constraint systems**. Entailment is PSPACE-hard as well, since
PSPACE is closed under complement. This transfer depends on the previously
recorded written/audited C030 and path semantics; it is not a new formalization
of the subtype bridge.

This supplies an explicit signature-preserving reduction rather than silently
importing hardness from a richer subtype signature. It does not prove PSPACE
membership, decidability of the unrestricted problem, or an unconditional
superpolynomial running-time lower bound.

## 3. A polynomial-size instance with one complicated witness (C050)

The product method suggests a further test of the bounded-skeleton route.
The obstruction is not merely a large repetition count. Some positive inputs
force a long word containing exponentially many distinct short factors.

Fix d>=1, and define C_d to be the concatenation of all d-bit binary numbers
from 0 through 2^d-1, each written least-significant bit first. For example:

    C_1 = 0 1
    C_2 = 00 10 01 11.

There are d+1 binary DFAs with at most 6d^2+3d states in total whose language
intersection is exactly {C_d}. Here is an explicit construction, implemented
in `counter_intersection.py`.

### Format and endpoint DFA

Require the first d-bit block to be 0^d. Thereafter track position modulo d
and whether the current block consists entirely of ones. On completing the
first 1^d block, enter a terminal accepting state. No earlier point accepts,
and no later input is permitted. This uses at most 3d states.

It enforces complete blocks, the initial zero block, and stopping at the first
all-ones block. It does not itself check incrementing.

### One DFA per bit

For each j=0,...,d-1, track position modulo d, the expected value e of bit j
in the next/current block, and a carry bit c. Before any first-block value has
been processed, e is unset. At the start of each block set c=1. On lower bits
h<j, replace c by c AND current_bit. At position j:

    if e is set, require current_bit=e;
    set e := current_bit XOR c.

Retain this new e for the following block. Accept only at completed block
boundaries after at least one block. The first block is exempt from the
prediction check and is handled by the format DFA. There are at most 6d states
per bit checker (d positions, three e values, two c values).

The conjunction of bit checks is exactly addition of one modulo 2^d between
successive blocks. Starting from zero, the first all-ones block appears after
exactly 2^d blocks. The format DFA forbids continuing past it. Thus the
intersection contains C_d and no other word. This is an all-length proof,
not an inference from testing short candidates.

### The compiled unique witness

C048 with r=d+1 now has exactly one witness:

    W_d = (E(C_d)00)^(d+1).

Its length is

    |W_d| = (d+1)(2d*2^d+2),

and its compiled state count k satisfies

    k <= 18d^2+11d+3.

Flags are polynomially many, so the whole binary instance has polynomial
encoding size in d. C030 again gives an always-satisfiable subtype realization
of polynomial size with exactly this separating path. The construction
therefore works with both the abstract and exact normalized subtype inputs.

The tested counts use reachable-state generation and are smaller than the
coarse proof bound:

| d | Input DFA states | Compiled states | Unique witness length |
|---|---:|---:|---:|
| 1 | 6 | 23 | 12 |
| 2 | 20 | 67 | 54 |
| 3 | 44 | 141 | 200 |
| 4 | 78 | 245 | 650 |
| 5 | 122 | 379 | 1,932 |
| 6 | 176 | 543 | 5,390 |

These finite values are implementation checks, not the asymptotic argument.

### Why a polynomial-size fixed-word skeleton cannot suffice

For a word z, let f_l(z) be its number of distinct contiguous length-l factors.
Consider any fixed skeleton

    s_0 u_1^a_1 s_1 ... u_t^a_t s_t

with fixed literal words s_i, fixed nonempty repeated words u_i, and arbitrary
nonnegative exponents a_i. Let its unexpanded body size be

    B = sum_i |s_i| + sum_i |u_i|.

**Elementary lemma:** every word z generated by this skeleton satisfies

    f_l(z) <= B*l, for l>=1.

Proof: a factor lying wholly in a literal component has at most its length
many possible starts. A factor lying wholly in a power component has at most
|u_i| possible values, one per phase. Together these contribute at most B.
After dropping empty components, there are at most B components, because
every literal or repeated base has positive body cost. Each boundary can be
crossed by at most l-1 distinct starting offsets. Assign each remaining factor
to a boundary it crosses; union counting gives at most
B+(B-1)(l-1)<=B*l. Exponents can be arbitrarily large without changing this bound.

W_d contains E(x) for every d-bit word x, as an aligned factor within E(C_d).
These are 2^d distinct factors of length 2d. Hence any fixed-word skeleton
containing W_d has

    B >= 2^d/(2d).

Because W_d is the only witness, **any existence-preserving family of fixed-word
skeletons for this positive instance must include a skeleton of at least this
body size**. Thus no polynomial-size fixed-word-skeleton cover exists in general,
even though an effective finite cover might exist. The statement remains true
if exponents are written in binary or constrained arithmetically: it bounds
the literal bases themselves, not the size of their exponent values.

### Ordinary straight-line grammars have the same obstruction

For a binary straight-line grammar with g concatenation productions, every
factor of length l>=2 crosses a concatenation boundary at its lowest containing
node in the unfolded derivation. Each production has at most l-1 crossing
factors. Repeated uses of a nonterminal produce the same expansion. Therefore

    f_l(z) <= g(l-1).

An ordinary straight-line grammar generating W_d must consequently have

    g >= 2^d/(2d-1).

This is a statement about ordinary terminal/concatenation straight-line
grammars, not about arbitrary programs, circuits, transducers, or higher-order
representations. The counting family has a short generating program; there is
no contradiction. This proof is included in full rather than relying on a
compression lower-bound citation.

## 4. Reproduction and limitations (E032)

Run from the repository root:

    python3 experiments/check_word_sync.py

The test uses only Python's standard library and the existing independent
border/bridge code. The saved output is `results/word-synchronization.json`.
It records:

* 32,767 raw binary words for the eleven-state universal equality fixture;
* 3,785 block tuples, including unequal words of equal length and equal counts;
* all 4,096 pairs of total two-state DFAs with fixed start, giving 1,858 YES
  and 2,238 NO, checked against all 61,440 common-word tests through the
  complete product-derived bound;
* 120 additional random lists, giving 19 YES and 101 NO, with an independent
  product traversal;
* 196 full/reduced subtype-summary comparisons and 20 exact canonical regular-
  model checks, including negative supplied paths;
* the counting family for d=1,...,6, all 642 single-bit corruptions of C_d,
  and exhaustive common-word identity checks through |C_d| for d<=2;
* 3,055 finite checks of the skeleton factor-count lemma;
* an explicit product-state cap returning UNKNOWN, and malformed-input guards.

In all, 4,222 product decisions are recorded, counting the complete two-state
corpus, the random lists, and six counting instances. Other named fixtures are
reported separately rather than silently folded into that total.

An initial test-harness call misread the `reduced` bridge's return signature;
that integration error was corrected before producing the saved result. No
semantic assertion or counterexample was inferred from that failed run.
No full repository suite, Lean proof, or independent review is claimed.

## 5. Revised target

C046 requires arithmetic synchronization of large lengths. C048 requires
synchronization of whole words and handles a genuinely nonflat class by a
finite product. C050 shows that replacing all those words by polynomial-size
fixed literal/power schemas, or by polynomial-size ordinary straight-line
grammars, is not a complete strategy.

None of these facts rules out a computable general witness bound or an
effective finite cover with superpolynomial-size members. They do suggest a
more suitable abstraction: finite regular constraints on shared word variables,
with products used for equality components. The present construction does not
reduce arbitrary BorderAvoid instances to that form. In particular it does not
bound the number of comparisons that must be represented, or justify an
existential-word-equation reduction for the universal internal suffix tests.
That coverage argument remains the missing step toward an unrestricted result.

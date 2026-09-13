# Exact exponential source-walk scheme cost and a switching-route audit

Date: 2026-09-13. Base main: `4ce1d6b5d20d3fa39a5c4f72d9c96da24e56356a`.
Workstreams A008/A017; implications for A009 and Q004.

**WRITTEN PROOF + REPRO; independent mathematical review pending; not Lean.
Neither result below supplies an unrestricted subtype-entailment decision.**

## Outcome and relation to earlier work

The attempted closing route allowed finite-control switching among shared
terminal suffixes. The supplied-description solver below is complete, but its
restriction placing every flag target in the final master overlaps the earlier
target-frontier regime. It does not handle arbitrary recurrent target/source
interactions. That failed generalization is retained, not promoted into coverage.

The new negative result is stronger than the previous source-VISIT bound:
unknown bases and arbitrary powers do not give a polynomial-COST cover in the
precise C075 syntax. In the family below the exact minimum scheme cost equals
the number of source visits. No powered phase can compress any of them.

The synchronization construction and binary-counter family are prior C048/C050
work, described in [the original proof](2026-09-05-word-synchronization.md).
The new contributions are the final universal component, genuinely live-source
certificates and same-phase window injectivity, giving an exact lower bound for
VARIABLE-base C075 schemes. No construction-priority claim is made.

## 1. Exact scheme syntax and counter family

Use the C075 syntax W=C0 U1 C1 ... Uh Ch. A phase is plain, or Ui=Bi^mi with
mi>=0, nonempty unknown closed source-walk Bi, an explicitly supplied list of
d_i source arrivals, and positive source-free-interior segments. Entry, positive
next-source bridges, and the source-free exit are exactly those of C075. Cost is
h+sum_i d_i; exponents and source-free word lengths are not charged. A bridge
is positive, so adjacent phases do not share their endpoint source position.

For integer d>=1, let Cd concatenate every d-bit integer from 0 to 2^d-1,
least-significant bit first. Its length is d*2^d. Use d+1 binary DFAs whose
intersection is {Cd}, as in C050. A self-contained implementation is in
[the checker](../experiments/scheme_cost_barrier.py).

The format DFA requires the first d bits to be zero, then whole d-bit blocks,
and stops at the first all-ones block. For each j in {0,...,d-1}, a bit DFA
tracks a position modulo d, an expected bit e in {unset,0,1}, and a Boolean
carry. At a block's beginning carry is true. Bits strictly below j conjoin
into the carry. At position j compare the bit to e when set, then set the
next expectation to bit XOR carry. Reset carry at the next block boundary.
Accept only at whole-block boundaries after an expectation has been set.
The first zero block and all expected updates force each successive increment;
format acceptance forces termination at the first 2^d-1 block. Thus the
intersection is the singleton {Cd}, at every length, not only tested lengths.
The format has at most 3d states; the bit DFAs have at most 6d each, for total
at most 6d^2+3d. Each transition advances a well-defined phase modulo d.

Append a one-state universal binary DFA as the LAST component. Apply C048 with
E(0)=10, E(1)=11 and delimiter 00. There are r=d+2 stages and

    k_d = 3*sum_i |Mi| + 2r + 1 <= 18d^2+11d+8.

In each stage the compiler has one entry tagged START, boundaries tagged with
the preceding data bit and underlying DFA state, data helpers, and a delimiter
helper. Helpers are unflagged. Flags go from earlier-stage entries/boundaries
to last-stage entries/boundaries exactly when predecessor tags differ. The
last accepting state is terminal. All states/stages and transitions are
explicit in the linked C048 construction and the independent implementation.

Its accepted words independently choose data ui from component Mi. C048's
rightmost-mismatch proof forces all ui equal, so the exact witness language is

    Witness(I_d) = { Wd },  Wd=(E(Cd)00)^(d+2).

For completeness, unequal ui and ur have a longest common suffix X preceded
by unequal data bits, or by START on one side and a bit on the other. The
suffix E(X)00 from the final block matches at the earlier block's corresponding
boundary and its unequal tags flag it. Equal data force equal offsets and tags:
the first delimiter of the earlier block must align with the terminal delimiter.
All relevant cuts are aligned code boundaries; incidental unaligned substrings
cannot supply flags. This handles empty data and empty common suffixes too.

## 2. Every source visited by Wd has a live outgoing flag

Keep the earlier-stage data equal to Cd, but change the universal final data.
For an earlier entry, choose final data 0Cd. At its post-first-bit boundary the
tag is 0 and the remaining suffix is E(Cd)00, matching the earlier START entry.
For an earlier data boundary after Pa in Cd=PaX, choose final data X. The final
entry tag is START, the earlier tag is a, and both tails begin E(X)00. The case
X empty is allowed by the universal component. These are accepted candidates
with genuine flagged comparisons, not merely reachability in a product graph.

Every source state visited by Wd therefore retains a live outgoing flag after
removing all semantically dead flags. Such removal preserves the witness language
because those flags never excluded any accepted candidate in the first place.
It also preserves the complete list of source POSITIONS in Wd. No broad claim
that every syntactic flag is live is needed or made.

## 3. Same-phase counter windows are injective

A length-d window of Cd starting at phase t modulo d uniquely identifies its
counter x. At t=0 this is the counter block itself. At t>0 the window gives
bits t,...,d-1 of x, followed by bits 0,...,t-1 of x+1. The first part gives
floor(x/2^t); subtracting one modulo 2^t from the second recovers x modulo 2^t.
The window therefore reconstructs x. Only starts for which the whole window
exists are considered. Distinct starts at the SAME phase cannot have equal
length-d windows, including windows crossing a block boundary.

Every state loop in a counter input DFA consumes a multiple of d bits, because
its state has a well-defined phase modulo d. An original compiled source-pivot
loop stays within one stage: the stage number increases at delimiters and
never decreases. Entries have no returning transition. A remaining source loop
consists of complete E-coded data tokens and projects to a positive loop in
one of the counter input DFAs. Its data length is at least d and divisible by d.

If this source-pivot loop occurred twice consecutively in Wd, the first d data
bits in its two copies would be equal windows of Cd at the same phase, which
has just been proved impossible. The final universal stage has no sources.
Thus EVERY active powered phase occurring in Wd has exponent at most one.
This concerns literal repetition in a word, not just transition-action equality.

## 4. Exact minimum, including after dead-flag pruning

A plain phase costs one and covers one source position. A one-copy phase with
d_i source arrivals covers d_i+1 source positions and costs exactly d_i+1.
Empty stars cost at least a plain phase and can be replaced by one. Bridges
have no source in their interiors and are positive, so the phase positions
partition all source positions without sharing or omission. Section 3 excludes
any higher exponent that could reduce the cost. Hence every scheme containing
Wd costs at least its number of source visits. Plain phases attain that value.

Each of the d+1 earlier stages has one entry and |Cd| post-data boundary visits.
There are no other sources on the word. Consequently

    min_scheme_cost(I_d) = (d+1)*(d*2^d+1).

Section 2 leaves precisely these source positions after removal of semantically
dead flags, so the same exact minimum holds after that pruning. Since the entire
constructed input has size polynomial in d, this disproves a polynomial-cost
existence-preserving cover by the EXACT C075 syntax, including its unknown bases
and unbounded powers. It also supplies exp(Omega(sqrt(k_d))) growth in state count.

It does NOT refute a larger total computable scheme bound, Q004, or an alternative
shared-word representation. Indeed these very instances are decided by the
existing DFA-intersection method with one common word. This is a representation
lower bound, not an unconditional runtime lower bound or an undecidability proof.
The exact general coverage implication remains unproved.

## 5. Exact finite-word cost computation and evidence

For a GIVEN accepted word, list its source cuts. At cut i a phase is plain or
uses a contiguous closed-walk base ending at cut j with the same state. The
base has j-i source arrivals. Every literal m-copy occurrence consumes exactly
m*(j-i)+1 source positions; the next bridge goes to the next source, if any.
Its cost is 1+(j-i). Enumerating all such bases/copy counts and taking a shortest
path over the ordered source cuts exhausts the grammar for that fixed word.
A Z-array accelerates exact equality; no hashes are used. A separate certificate
checker verifies the partition, loop states, counts and literal powers.

The program does not equate a fixed-word optimum with general witness synthesis.
For this family, the singleton theorem is what makes the computed optimum the
instance optimum. A separate recursive literal-partition oracle checks the
optimizer on 244 short accepted words, including words that are not witnesses.

The reproduced family results are:

| d | States | Unique witness bits | Exact minimum cost |
|---:|---:|---:|---:|
| 1 | 28 | 18 | 6 |
| 2 | 72 | 72 | 27 |
| 3 | 146 | 250 | 100 |
| 4 | 250 | 780 | 325 |
| 5 | 384 | 2254 | 966 |
| 6 | 548 | 6160 | 2695 |

The all-d assertion rests on the proof, not extrapolation from these six rows.
The suite additionally checks 518 complete common-word cases through the relevant
bounds for d<=2; 642 bit corruptions; 565 distinct-source liveness certificates;
20,320 agreements of literal forward/reversed, Z and KMP word predicates; 8,158
phase-window reconstructions through d=9; and 54 phase-aware input automata.
The [compact results](../results/scheme-cost.json) are deterministic. A supplied
`--full-output` path regenerates every literal certificate and optimal partition.

## 6. Alternative switching route: exact class, not new general coverage

The [switching implementation](../experiments/suffix_switch.py) takes a positive
reference count h, data alphabet {0,1}, distinct tokens M0,...,M(h-1), END and
SWITCH, plus a finite deterministic controller and regular edge/master/output
guards. Choose shared binary words v0,...,v(h-1), and put

    T_j = Mj vj M(j+1) v(j+1) ... M(h-1) v(h-1).

A candidate follows a controller path with reference labels j1,...,jm and has
form T_j1 END ... T_jm END SWITCH T_0 END. Every edge's guard must accept its
reference T_j, the master guard accepts T_0, and the output guard accepts the
whole word. m may be zero and every vi may be empty. All regular automata are
explicit partial DFAs; undefined transitions reject. Duplicate source/label
control edges are disallowed, making the compiled candidate automaton deterministic.

The actual candidate automaton allows independently chosen data in earlier units.
It tracks unit/master phase, predecessor token, the relevant regular guard state
and output-guard state. It has a unique terminal final mode. Flag post-token cuts
from unit kind j to master phase l whenever j<=l and the predecessor tokens differ.
There are no flags before initial markers or at helper states. Two independent
words beginning with the unique marker Mj cannot be distinct and suffix-comparable
as WHOLE reference words, since that marker occurs only at their beginning. If
unit data differ from the master's j-reference, their rightmost mismatch has
different predecessors and a common suffix ending at END, yielding a flag. Equal
references align the unique terminal END and every marker; aligned predecessor
tokens are equal, so no flagged comparison occurs. Thus the compiled instance's
witnesses are exactly the shared-reference candidates described above. A fixed-
length injective token-to-binary encoding with flags only at token boundaries
preserves both implications. No new subtype constructor is introduced.

For a complete algorithm for this SUPPLIED description, take the disjoint union
of all guard states and one rejecting sink. A data word acts as a transformation
on this finite set. Enumerate the finite monoid generated by data letters 0 and1,
retaining one representative per action. If its size is M, shortest representatives
have length at most M-1. Enumerate all M^h joint assignments for the shared vi.
The action of every reference, and truth of every edge/master regular guard,
then follows by composition with the fixed marker actions. All uses of a shared
vi use one action, not independent choices.

For a tuple passing the master guard, explore the finite graph (controller state,
output-guard state). An enabled j-edge applies the action of T_j END. A vertex
accepts exactly when its controller state is final and applying SWITCH T_0 END
would accept the output guard. This graph has at most |control|*|output states|
vertices before the rejecting sink is discarded. A successful path reconstructs
all data and switches; exhaustive failure for every action tuple is NO. Optional
resource caps produce UNKNOWN. Completeness follows because any actual data words
induce an enumerated tuple, and replacing them by its representatives preserves
ALL guards and shared reference identities. The accepted controller/output path
can then be shortened by ordinary finite-graph reachability in this exact class.

The [independent checks](../experiments/check_suffix_switch.py) compare the semantic
parser, literal token predicates and binary predicates on 1,452 structured cases.
They exhaust 16 finite compiled languages (2,426 candidate words) and 60 fixed-
master finite graphs: 15 YES,61 NO overall. They also check 8,191 raw binary words,
noncommuting references, empty data/zero units, incompatible shared assignments,
and caps. The demo has v0=0,v1=1 and reference sequence 0,1, with
T0=M0 0 M1 1 and T1=M1 1; T0T1 differs from T1T0.

**Failed closing implication:** all targets lie in the terminal master, which
has a supplied finite marker structure. This overlaps the earlier C054-C056
[target-frontier approach](2026-09-06-target-frontier.md). Neither the switching
solver nor the cost theorem gives a complete cover for general recurrent targets.
No separate new coverage theorem is inferred from passing these checks.

## 7. Reproduction and handoff

From the repository root with Python3.10+ and no third-party packages:

```sh
python3 experiments/scheme_cost_barrier.py --self-test --output /tmp/scheme-cost.json --full-output /tmp/scheme-cost-full.json
cmp results/scheme-cost.json /tmp/scheme-cost.json
python3 experiments/check_suffix_switch.py --output /tmp/suffix-switch.json
cmp results/suffix-switch.json /tmp/suffix-switch.json
```

Canonical IDs and review status are in
[the ledger supplement](../research/SCHEME_COST_BARRIER.md).
For the constructive route, do not assume polynomial C075 cost and do not
confuse finite-control switching under a fixed terminal master with arbitrary
recurrent-target coverage. A larger computable cover is still a viable question.
For the opposing route, description growth and copied counter words are not a
computation reduction: a real undecidability argument must preserve both directions
of the ORIGINAL terminal predicate. No Lean build, independent mathematical
review, unrestricted decision or scientific-priority claim accompanies this work.

# Necessary nonflat runs and a last-flag decision certificate

Date: 2026-09-05. Base: `5ee18c63d3a18a524a21a9ae1ddc803904f8e405`.
Approach A017; claims C035-C037; experiment E025.

**Status: WRITTEN PROOF + IMPLEMENTATION + REPRO. Not Lean-checked.**
This does not settle unrestricted Problem 1.7. It refutes one possible finite
cover strategy and gives a different exact certificate that works for some
nonflat terminal instances. The terminal-to-subtype transfer uses C030.

## 1. Every witness can require a nonflat edge support (C035)

Consider the following partial binary DFA, with start 0, sole final 5,
no Bad states, and G={(0,3),(1,3)}.

| State | 0 | 1 |
|---|---|---|
| 0 | 1 | undefined |
| 1 | 2 | 3 |
| 2 | 2 | 1 |
| 3 | 4 | undefined |
| 4 | undefined | 5 |
| 5 | undefined | undefined |

Its accepted language is `0 (0^r 1, r>=1)* 101`. State 3 occurs exactly
once on an accepted run, immediately before the final suffix `01`. Only this
suffix can be a flagged target. Its earlier occurrences are classified as
follows.

* With zero complete returns through states 1 and 2, the word is `0101`.
  Its initial occurrence of `01` violates (0,3).
* With at least one return, the initial two letters are `00`, so (0,3)
  cannot be violated. A return with r=1 reads `01` from state 1 and violates
  (1,3). A return with r>=2 starts with `00` from state 1; its later `01`
  starts at state 2, which is not flagged into 3.
* The last visit to state 1 begins the exit `101`, which does not start
  with `01`. There are no other flagged comparisons.

Therefore the exact witness language is

    0 (0^r 1, r>=2)^+ 101.

The unique shortest witness is `0001101`, of length seven. Every witness uses
all seven defined edges. In particular it uses the self-loop at state 2 AND
the cycle 1 --0--> 2 --1--> 1. Their common SCC has two internal labelled
outgoing edges from state 2, so the edge support is nonflat.

**Consequence.** No flat edge subautomaton contains any witness, even though
the full instance has one. Enumerating all flat edge restrictions is NOT a
complete existence-preserving cover. This does not refute bounded word
skeletons with richer fixed blocks: `0 (001)^t 101`, t>=1, already supplies
some witnesses of this example. No six-state minimality claim is made.

The two flags are individually essential to this obstruction: removing
(0,3) permits the flat path `0101`; removing (1,3) permits `001101`, using
the outer cycle but not the inner self-loop. The exact budget is two, checked
by exhausting all three lower-budget sufficient searches and validating
`Sufficient(2,0)` on `0001101`. No global terminal-budget bound is refuted.

C030 realizes this instance with 13 subtype variables, preserving each word.
Thus failure of flat-edge coverage also occurs on actual normalized subtype
inputs, under the recorded status of that reduction.

## 2. Terminality really does imply nonmerging (C036)

Let w be any defined accepted word of a DFA whose accepting states are
terminal. Write n=|w| and c(t) for its state at position t. Suppose i<j and
w[i:i+n-j]=w[j:n]. Then

    c(i+t) != c(j+t), for every 0<=t<=n-j.

If the two states were equal at some t, determinism on the remaining common
letters would put the earlier occurrence in c(n), an accepting terminal,
at position n-(j-i)<n. The full run could not continue, a contradiction.
The same argument also excludes any accepting state on the earlier run.

This is stronger than merely observing different initial states, and its
terminal hypothesis is indispensable. It does not rehabilitate the rejected
nonterminal rigidity equivalence in C006.

**Corollary.** In the partial order of suffixes of w under the prefix relation,
every chain has at most k elements, where k is the number of states. Two
comparable distinct suffixes cannot begin in the same state, so all states
on a chain differ. This bounds chain height, NOT suffix lengths, witness
lengths, or the number of incomparable suffixes. C032 remains nonregular.

## 3. Only the last aligned flag matters (C037)

First fix one final f. Remove Bad states, diagonal-flagged states, and every
p with G(p,f); these are precisely mandatory boundary exclusions. Trim to
states reachable from the start and able to reach f. Other terminal finals
cannot belong to this slice. Let r be the remaining number of states.

Build a synchronized pair graph. Vertices are ordered pairs (p,q) of distinct
live states with p!=f. An edge labelled a goes to
(delta(p,a),delta(q,a)) when both transitions are live, the left target is
not f, and the target states differ. Endpoints are (p,f), p!=f.
Every actual proper suffix agreement traces a path in this graph by C036.
A root may be a flagged pair (p,q) with both states nonfinal and q reachable
from p; this last condition is a sound coarse check on occurrence order.

There is an important improvement over requiring this whole graph acyclic.
Take a violated comparison whose target suffix has MINIMUM length. If its
synchronized path visited G again after t>0 letters, the positions i+t,j+t
would give a shorter violated suffix. Hence no positive-time vertex of this
path belongs to G. In particular an arbitrarily long comparison can be
irrelevant because a later flag already supplies a short violation.

Define the **last-flag graph** by allowing a flagged vertex only as a root.
All positive successors must be unflagged. Trim this graph to vertices
reachable from its roots and able to reach an endpoint (p,f).

**Theorem.** If this graph is acyclic, let H be the largest root-to-endpoint
path length, or zero if there is no such path. Then, on the chosen slice,

    Witness(w) iff Necessary(w,H,0), for every finite word w.

The forward implication holds for every instance. For the reverse, a word
passing the necessary predicate is boundary-safe. If it were not a witness,
choose a shortest violated proper suffix. Its pair path lies in the trimmed
last-flag graph, so its length is at most H, and the necessary predicate would
have detected it. This is a contradiction.

A longest DAG path computes H effectively. There are (r-1)(r-2) possible
internal distinct pairs of nonfinal states. A relevant path uses one flagged
root, unflagged internal vertices without repetition, and a final endpoint.
Consequently

    H <= max(0,(r-1)(r-2)).

This is a bound on the shortest VIOLATING SUFFIX needed to detect a bad word.
It is neither a bound on every agreement nor the instance budget B=min(L+D).
For example, a flag-free long singleton language has H=0 but positive budget.

For fixed H, the existing finite Necessary automaton is exact by the theorem.
Its exhausted graph therefore decides YES/NO for the slice. Union over final
slices decides the full instance when every nonempty slice is certified.
The graph-size cap and the word-automaton cap preserve UNKNOWN. A cycle means
only that this certificate is unavailable; it does not prove any answer to
unrestricted entailment, or even that the potential long comparison is
realized by a single word.

### Product cycles can be harmless

Take C032's four-state automaton and add flag (0,2) to its original (0,1).
The synchronized pair (0,2) has a productive zero-loop, but it is now flagged.
The last-flag graph drops edges entering it, computes H=1, and proves the
entire witness language empty. Looking only for cycles in the full pair graph
would miss this exact NO certificate.

### The nonflat obstruction is nevertheless decided

For Section 1, only the two-letter suffix `01` can be a flagged target, and
the algorithm obtains H=2. Its finite Necessary(2,0) graph returns `0001101`.
Adding flag (2,3) gives a nonflat negative instance: the final `01` necessarily
has an earlier occurrence starting at 0, 1, or 2. The same certificate proves
NO. Thus candidate-graph nonflatness alone is not the remaining obstruction.

## 4. Tests and precisely scoped results

Run `python3 experiments/check_nonflat_overlap.py` from the repository root.
The deterministic result is `results/nonflat-overlap.json`.

* The obstruction: all 8,191 words through length 12 agree with the regular
  formula and with its subtype realization; 521 exact canonical regular
  models are independently checked. All 128 edge subgraphs are examined;
  all 127 proper subgraphs are flat after productive trimming and have exact
  negative graph certificates. Seven have nonempty candidate languages.
* On all 65,536 normalized four-state terminal cases, the NEW certificate
  alone gives 45,158 YES, 20,090 NO, and 288 UNKNOWN. Every definitive answer
  agrees with the earlier complete C034 oracle. This includes 2,136 cases
  with nonflat productive candidate graphs: 1,856 YES and 280 NO.
* With seed 2026090537, 600 additional random terminal automata give 232 YES,
  365 NO, and 3 UNKNOWN. Across certified final slices there are 62,220
  direct/reversed/necessary predicate comparisons and 566 checked nonmerging
  agreements. The largest detection bound in this sample is four.
* Caps, nonterminal inputs, empty instances, multiple finals, Bad states,
  diagonal flags, and cyclic residuals retain their documented verdicts.

The original `experiments/run_experiments.py` was also rerun: its 10,160
word checks and 121,920 automaton comparisons reproduce the committed result
byte-for-byte (Git blob aa6d1680b5442493744c667024d2df77a1bd8e78). The full
repository suite, repository-wide link scan, and Lean build were not rerun.
The tracker was regenerated from its registry using a renderer first checked
against the unchanged baseline output.

The old corpus remains an oracle, not a new all-state bound. The proofs in
Sections 1-3 are independent of the finite counts. The optional arithmetic
backend is imported by the flat-cover helper but is NOT invoked by E025.
The experiment needs only the Python standard library.

## 5. Failed routes, literature context, and the remaining obligation

This attempt started with a flat-edge-subgraph cover and refuted it in
Section 1. An initial acyclic-FULL-pair criterion was sound but weaker;
Section 3's shortest-violation argument correctly removes later flagged
vertices and replaces it. Neither criterion may turn a cyclic residual into
NO. No global witness-length or successful-budget bound has been proved.

A bounded source check located Anderson et al., *Detecting Palindromes,
Patterns and Borders in Regular Languages*, arXiv:0711.3183, Theorem 58 and
Corollary 62: ordinary unbordered-word existence in an n-state NFA has a
6n+1 length test. The parsed theorem statement was checked; remote PDF page
rendering was unavailable in this environment. No proof transfer is claimed.
Our flags constrain pairs of internal suffix starts, not just the two ends
of one word; the ordinary unbordered theorem cannot be substituted unchanged.

The next target is the cyclic, unflagged, productive part of the synchronized
pair graph. A complete argument must either control those long comparisons
while preserving terminal acceptance, or show how to cover their possible
witnesses by a finite effective set of richer skeletons. The existing flat
arithmetic procedure and C029 remain separate certified components. C035
rules out only flat EDGE restrictions, not a bounded-skeleton theorem.

# Flag transport, an essential separator obstruction, and its nonflat repair

Date: 2026-09-08. Base main: `c4875e599958dd624dd7220dd7cbe5bb96822b11`.
Workstreams: A017/A012. No additional agents were launched.

**Status: written all-length arguments and executed independent-algorithm
checks; independent mathematical review pending; not Lean-checked. This is
not a solution of unrestricted Problem 1.7.** The contribution combines the
latest separator and semantic-tail constructions, disproves their proposed
unrestricted negative convergence at fixed annotations, and supplies a
witness-language-preserving annotation rewrite which repairs the obstruction.

## 1. Reviewed baseline and exact target

The baseline includes the semantic marker-tail and synchronous separator
continuations, and the repaired PR #12/#14 material merged through PR #21.
The latter's head `aab92a10e3b305bbfe1f88e141f922b5d48c2030` has a successful
Research checks workflow, run 34218626457. That CI result concerns its own
checked tree, not this new contribution and not a formalization of new proofs.
PR #16 retains the explicit fixed five-state certificate; it is not silently
merged by this investigation. PR #19 remains an older overlapping repair PR.

Also read the unmerged single-source strategy and shape-lemma submission at
`6b7c473efa2e6e836b872737e2d948e58098293a`. Its missing primitive-root and
new-border obligations remain genuine proof obligations. Section 8 records a
specific overstatement in the accompanying strategy note; this does not
refute all of its separate conditional shape lemmas.

The attempted closing claim was: after choosing comparison-preserving
transition separators, does some finite semantic separator-tail budget refute
every terminal NO instance? The answer is NO even with all flags essential.
The counterexample also survives replacing full pair-graph synchrony by the
weaker requirement that the encoding preserve witnesshood on every word.

The original signature remains bottom and binary product over arbitrary,
possibly infinite trees. The internal alphabet `01#` below is just a decoded
view of the existing paired binary encoding, not an additional constructor.

## 2. Exact common-reference search with a distinguished separator

Let J be a finite terminal DFA over a finite alphabet D union {#}, where # is
not a data letter. Require every transition entering an accepting state to
read #; handle an accepted empty word separately. Boundary normalization is
unchanged: remove Bad, diagonal flags, and sources flagged into the selected
final. Define Tail_H to exclude proper flagged agreements whose target suffix
contains at most H occurrences of #.

For each fixed finite H, Tail_H existence is decidable by the existing
semantic-tail construction generalized from unary data to D*. The
implementation is `experiments/separator_tail.py`.

### Why general data still give an exact finite construction

Every nonempty candidate splits uniquely as u_0# ... u_(m-1)#, with u_i in D*.
Set r=min(H,m). The final r blocks are references. If r=H, an arbitrary prefix
of complete blocks is allowed. If r<H, the prefix must be empty. Enumerating
reference start/end states and separator successors gives a finite set of
schemas; it does not bound the number of earlier blocks.

A reverse padded convolution chooses ALL reference words consistently. It
retains the current reverse state of each reference, whole-word equality bits,
and persistent equal-tail flag-hit bits. For reference blocks i<j a hit is a
violation exactly when all subsequent whole-block equalities hold:

    hit(i,j) and AND_{h=1,...,r-1-j} equal(i+h,j+h).

The first separator must align at the same offset in matching suffixes.
Before that separator, the data tails must be equal. Every later whole target
block must match its corresponding source block. This proves necessity and
sufficiency, including overlap, empty data, and flags immediately before #.
Distinct cuts in one data block cannot agree, since their first # offsets
would differ.

Along the SAME reverse convolution maintain every possible source descriptor

    (source endpoint, current state, reference-equality mask,
     persistent flag-hit mask, finished).

Each reverse data edge or finish/padding choice has its literal usual meaning;
union is an exact powerset image. This is not permission to pick different
reference words for different source observations. After all references finish,
an unfinished source has no remaining whole-word equality and can acquire no
new equal-tail hit. Its unmatched left part reduces to finite reverse data
reachability. A source longer than the maximum reference length M therefore
has an observation-equivalent representative of length at most M+k.

A forward prefix monitor retains the current original state and all pending
reference suffixes that a prior hit still needs to match. Equality advances an
obligation; a mismatch discards it; completion rejects. At the reference cut,
remaining obligations are evaluated against the same whole-reference equality
matrix. This checks precisely all prefix-to-reference comparisons. All targets
retained by Tail_H are in those references; no restriction is put on the
original state labels visited in the prefix.

For reconstruction, the new code replays the finite descriptor set against the
selected reference tuple, then completes a longer source by finite reverse
reachability. It does NOT enumerate all data strings up to a guessed length.
The selected source word is independently checked against the literal equality
and hit definition. This replaces the old unary source-recovery loop.

There are at most 2 k^2 4^r source descriptors and at most

    S(k,r) = (k+1)^r * 2^(r(r-1) + 2 k^2 4^r)

reference/powerset states. The prefix monitor has at most k*2^(r-1) states.
Thus the uncapped fixed-H computation terminates. Finite alphabet size affects
branching, not the finiteness argument. The previous loose bound

    (r + k*2^(r-1)) * (S(k,r) + k + 1)

still bounds a successful instantiated schema. It bounds the relaxation, not
some witness of every unrestricted positive instance.

### Exact weighted spectrum and status rules

The existing joint action on single states and last-aligned synchronized pairs
works over this alphabet as well. For a periodic marked comparison

    w=x(uv)^e u,  v nonempty,  1<=e<=k-1,

the target cost is e*count_#(u)+(e-1)*count_#(v). Use weight one on # edges
of the action Cayley graph and zero on data edges. Only positive-cost cycles
make a fibre unbounded; zero-cost cycles can represent arbitrarily long data.
The e=1 coefficient of v is zero and is handled separately. Nonempty identity
representatives are preserved. This is the prior weighted proof, with the
alphabet dependence made explicit, not a new general witness bound.

A bounded last-aligned separator spectrum with maximum H makes Tail_H exact.
An exhausted NO for any Tail_H is an unrestricted NO certificate. A Tail_H YES
is only a relaxation result unless its word passes the original witness
predicate or exactness was proved. Unbounded spectra and all resource caps
remain UNKNOWN for unrestricted existence.

## 3. A nine-state, essential-flag counterexample to all separator budgets

Use start 0, sole terminal final 4, no Bad states, and

    G = {(0,2), (0,3), (5,6)}.

| State | 0 | 1 |
|---:|---:|---:|
| 0 | 6 | 5 |
| 1 | 6 | 5 |
| 2 | undefined | 7 |
| 3 | 8 | 7 |
| 4 | undefined | undefined |
| 5 | 1 | undefined |
| 6 | 2 | undefined |
| 7 | 3 | undefined |
| 8 | 4 | undefined |

Every state is reachable and can reach final. The accepted language is exactly

    W(n,m) = (10)^n 00 (10)^m 00,  n>=0, m>=1.

This follows by the initial 0/1-to-helper phase, a single transition into state
2, and the second 3/7 phase. Parse in aligned length-two tokens: occurrences
of the substring 00 alone are not sufficient, since tokens can overlap it.

### Exact trichotomy, including the cut positions

Each accepted word has exactly one forbidden comparison:

| Case | Cuts (i,j) | Flag | Target suffix |
|---|---|---|---|
| n<m | (0,2(m+1)) | (0,3) | (10)^n00 |
| n=m | (0,2(n+1)) | (0,2) | (10)^n00 |
| n>m | (2(n-m)-1,2n+1) | (5,6) | 0(10)^m00 |

For the first two flags, state 0 occurs only at the beginning; alignment of the
first 00 token forces the stated remaining number of 10 tokens. State 2 occurs
once, and state 3 occurs only after at least one second-block token. Thus the
first flag realizes precisely equality and the second precisely n<m.
For (5,6), state 6 occurs only in the first delimiter, while earlier state-5
occurrences are the zero halves of first-block 10 tokens. The suffix begins
with that zero, then m copies of 10, then 00. Exactly one such first-block cut
exists iff n>m. These exhaust G; no boundary flag is present.

Therefore the instance is NO for all lengths. Every flag is essential:
removing (0,3) admits W(0,1), removing (0,2) admits W(1,1), and removing (5,6)
admits W(2,1). Consequently deleting redundant flags is not a repair.

### Separator colours forced by ONE real comparison

Let a Boolean marking m(p,a) select which transition receives a separator in

    a -> a [# if marked].

In the actual forcing word W(2,1)=1010001000, the unique comparison has cuts
(1,5) and the aligned pair path

    (5,6) -0-> (1,2) -1-> (5,7) -0-> (1,3)
          -0-> (6,8) -0-> (2,4).

Comparison preservation therefore forces

    m(5,0)=m(6,0),  m(5,0)=m(7,0),  m(6,0)=m(8,0).

The edge (8,0) enters final, so it is marked. All four zero-half edges
(5,0),(6,0),(7,0),(8,0) are therefore marked. In particular the first and
second data-token cycles acquire separator cost. This is not an artefact of
an unrealizable pair-graph path: the displayed single word realizes it.

The same necessity holds under the WEAKER requirement that the compiler merely
preserve witnesshood for every accepted word. The code has unique decoding,
so an encoded flagged agreement always decodes to an original agreement.
W(2,1) has only the displayed original violation. To keep this bad word bad,
that comparison must survive; equal encoding requires exactly those aligned
separator choices. Thus even a more selective synchrony certificate cannot
avoid the forced class for this fixed annotation and encoding form.

### Every finite H has a survivor

For W(n,n+1) the unique target suffix is (10)^n00. Every permissible marking
above gives it at least n+1 separators. Hence for every finite H, choose n>=H:
the encoded word satisfies Tail_H although it is not a witness. The minimal
full-synchronous colouring has exactly n+1 separators in this suffix.

This refutes completeness of increasing separator-tail budgets even AFTER the
proposed finite transition colouring, with essential flags and actual-word
synchrony. It does not refute arbitrary encodings, flag rewrites, fixed-skeleton
arithmetic, or decidability. The nine-state example itself has flat support.

## 4. Exact flag transport: change annotations without changing witnesses

Let g=(p,q), with p!=q and p,q nonfinal. Suppose:

1. Exactly one letter a is defined from both p and q.
2. Put r=delta(p,a), s=delta(q,a). They are distinct and neither is the start.
3. The entire incoming-transition set of r is {(p,a)}, and that of s is
   {(q,a)}. These are table-wide conditions, not sampled path conditions.

Then, on EVERY admissible accepted word,

    a violation of (p,q) exists iff a violation of (r,s) exists.

**Forward.** The target cut for (p,q) is not the end, since q is nonfinal.
Its first letter and the matching source letter must be the common a.
Advance both cuts by one. Their states become r,s; removing the leading
common a preserves the remaining suffix agreement. The new suffix can be
empty, which correctly includes a flag into the final state.

**Reverse.** Neither new cut can be position zero, since r,s differ from the
start. Their unique incoming transitions force the preceding states p,q and
the same preceding letter a. Move both cuts backwards one position and prepend
a to the matching substrings. Order is preserved and this gives an original
flagged agreement. Distinct endpoint states exclude diagonal comparisons.

All other flags and Bad annotations are untouched. Nonadmissible words fail
both witness predicates independently. Therefore replacing g by (r,s), or
reversing this rewrite, preserves the ENTIRE witness language, not just
existence. It does not preserve comparison positions, individual flags,
agreement profiles, overlap classification, or any particular budget.

These hypotheses cannot simply be dropped. The checker contains separate
counterexamples for an extra incoming edge, a destination equal to the start,
and a second common outgoing letter.

A finite graph on at most k(k-1) ordered distinct state pairs contains all
such local equivalences. Each flag may be replaced by any pair in its connected
component, carrying a finite path of verified rewrites. Finite enumeration of
placement tuples consequently preserves witnesshood. The code minimizes the
number of cyclic marked edges, then marked edges; this score is a heuristic,
NOT a completeness theorem. A capped placement search retains a valid candidate
but labels optimality UNKNOWN.

### Repair of the nine-state obstruction

For (5,6), common letter 0 leads to (1,2), whose incoming transitions are
uniquely those two zero-half edges. Transport (5,6) to (1,2). The accepted words
and their witnesshood are unchanged. The minimal synchronized marking now
marks only (6,0),(8,0), the two logical delimiters. No data cycle is marked.
The weighted spectrum is exactly {1}; the shared-reference solver proves NO
at H=1, exhausting five schemas. It uses 37 joint actions, compared with 49
and an unbounded spectrum before transport.

The rewrite is not cosmetic: the helper-level > comparison overlaps by one
letter, whereas advancing both cuts removes that artificial overlap and
exposes the logical token boundary. Keeping exact flag positions while
choosing separators was a stronger requirement than preserving witnesses.

## 5. A genuinely nonflat eleven-state extension

To rule out the interpretation that the barrier and repair are only about flat
graphs, use start 0, sole final 5, no Bad, and

    G = {(0,2),(0,3),(0,4),(6,7)}.

| State | 0 | 1 |
|---:|---:|---:|
| 0 | 7 | 6 |
| 1 | 7 | 6 |
| 2 | 7 | 8 |
| 3 | 7 | 9 |
| 4 | 10 | 8 |
| 5 | undefined | undefined |
| 6 | 1 | undefined |
| 7 | 2 | undefined |
| 8 | 3 | undefined |
| 9 | 4 | undefined |
| 10 | 5 | undefined |

Decode aligned a0 tokens to a. The underlying six-state graph is the prior
reset-marker obstruction. Its candidates have an initial 1^n0, any number of
intermediate reset blocks whose 1-count is zero or odd, and a final 1^m0 with
positive even m. All internal zeros reset to state 2, and the final zero goes
to final 5. Its SCC containing 2,3,4 has multiple overlapping cycles; encoding
does not turn it into a flat edge graph.

The same trichotomy compares the initial run to the FINAL run. For n<m, the
matching final-run cut lies in 3 or 4; for n=m it is in 2; for n>m the first
run has a state-1 cut corresponding, after encoding, to the helper flag (6,7).
Thus every candidate is bad, independently of the intervening reset blocks.
Each of the four flags is essential, as the words W(0,2), W(1,2), W(2,2), and
W(3,2) demonstrate on removing the matching case flag.

W(3,2) has a unique helper comparison and aligned path

    (6,7) -0-> (1,2) -1-> (6,8) -0-> (1,3)
          -1-> (6,9) -0-> (1,4) -0-> (7,10) -0-> (2,5).

The final zero-half edge (10,0) forces ALL zero-half edges (6..10,0) to be
marked. The reasoning again needs only preservation of that one bad word.
For arbitrarily large odd n, W(n,n+1) is accepted and has just one violation,
with target cost at least n+1. Every finite separator tail budget survives.
This is an all-length nonflat obstruction to the fixed-annotation combination.

Transport (6,7) across 0 to (1,2). Now only (7,0),(10,0) are marked. A marked
cycle STILL exists and is reachable from relevant targets; simply enforcing
C053's no-marked-cycle or C056's target-cone condition still does not suffice.
However each separator resets to state 2 or ends at final 5. If an agreeing
target suffix contained two separators, both aligned runs would merge at the
first reset, contradicting terminal nonmerging. Therefore H=1 is exact.

The combined implementation computes that H=1 using 97 joint actions and
proves NO by exhausting seven reference schemas. Before transport it reports
an unbounded spectrum using 157 actions and correctly leaves existence UNKNOWN.
This is a case for the semantic-tail combination, not just the old C053 cover.

Removing (0,2) gives a positive companion with an infinite family W(n,n) for
positive even n. The transported solver returns 101000101000. The original
and relocated annotations have exactly the same nonempty witness language,
but their separator-spectrum certificates differ. Thus the phenomenon is not
an artefact of comparing two empty witness languages.

## 6. Executed checks and exact evidence level

Command: `python3 experiments/check_flag_transport.py`.
Seed: 2026090881. Output: `results/flag-transport.json`.

- All 266 binary terminal tables through three states, with all effective
  off-diagonal nonfinal flag sets: 1,034 normalized instances. There are 3,139
  accepted-word annotation/encoding checks through length seven and 24 local
  transport proof edges, compared on 76 accepted words.
- 160 additional random tables through seven states with Bad, boundary flags,
  and varied starts: 40,800 raw-word witness comparisons and 6,034 defined-word
  exact encoded-comparison checks.
- 220 complete acyclic-language oracles over 01#: 435 accepted words in full,
  880 exact relaxation queries (458 YES/422 NO), 220 exact existence decisions,
  and 118 independently enumerated exact separator-spectrum maxima.
- 97 actual reference tuples from 100 attempts: complete observation sets agree
  against 41,330 literal source-word checks at the proved M+k source bound;
  all 975 observations are independently reconstructed. Three attempts had
  no usable reference, rather than silently being counted as successful tests.
- 193 action graphs retained from 200 generator attempts, with 2,361 weighted
  fibre checks against independent reachability and path-cost DP. Seven graphs
  above the oracle's 100-vertex limit are omitted; no all-graph census is claimed.
- Nine-state obstruction: 1,056 parameter pairs, 131,071 binary words through
  length 16 (21 accepted), all 2,048 transition markings, four globally valid
  synchronous markings, and 32 markings preserving the forcing-word comparison.
  The 300 escaping-family identities and returned tail survivors are retained.
- Nonflat extension: 430 accepted reset-language words through decoded length
  12, 210 two-block pairs, 192 escaping-tail identities, four essential-flag
  witnesses, and ten positive-family members.
- The previous three-state target-recurrent separator fixture is now returned
  YES with 01; its semantic separator spectrum is finite. Additional infinite
  two-data-letter cases have direct all-length truth arguments.
- Five malformed-input guards, three intentional cap-to-UNKNOWN guards, and
  three counterexamples to dropping transport hypotheses are preserved.

The tests are algorithmic cross-checks, not an independent human proof review.
They do not prove the all-length theorems. The replay of the supplied standalone
last-flag package also passed. The unchanged original core suite was recovered
with its verified source hash and rerun: 10,160 word checks and 121,920
automaton comparisons reproduce result blob
`aa6d1680b5442493744c667024d2df77a1bd8e78` exactly. Original `border_lab.py`,
`lastflag_spectrum.py`, and `run_experiments.py` remain byte-identical to their
pinned Git blobs.
No full local repository CI, repository-wide link scan, or Lean build is
claimed. The package includes an integration script, not an assertion that its
contents have already been committed remotely.

## 7. Closing attempt, failure, and remaining obligation

The direct proposed closing strengthening is now refuted. Combining current
synchronous separator choices with arbitrarily large semantic tails is NOT a
complete NO semiprocedure on fixed annotations, even if every flag is essential
and only real marked comparisons constrain the encoding. The new nine- and
eleven-state examples are not evidence for undecidability; their repairs are
constructive and exact.

The repair suggests expanding the object being normalized: not just candidate
words or transition encodings, but the SEMANTIC presentation of flag obligations.
There is now an executable finite language-preserving transport relation, and
it can change an unbounded separator certificate into a bounded one. That is
useful structure, not an all-input normal-form theorem.

What remains unproved is that every positive instance has an effectively
bounded shared description, or that every NO instance has an equivalent
presentation certified by some finite separator tail or another finite proof.
Enumerating a finite local transport orbit terminates, but there is no proof
that these particular orbits are complete for that purpose. Nor does optimality
of the cyclic-edge score imply optimality for existence or certificates.

A candidate global theorem must preserve common word assignments across
DIFFERENT comparisons and must account for all newly generated crossings. The
finite monoid here deliberately preserves one marked comparison; it is not a
substitutive summary of every possible left context. Existing shared-word
residual collisions remain relevant. No unconditional computable witness bound,
complete negative calculus, or undecidability reduction is asserted.

The external negated-containment flattening and regular-expression universality
leads were checked for scope. One negated containment of fixed terms is not
our universal quantification over all coloured internal cuts; undecidability
of richer single-variable backreference expressions is not a reduction into
terminal-copy patterns. No external theorem was used to bridge that gap.

## 8. Specific review correction in the single-source strategy branch

The strategy note at `6b7c473` states that pairs along a shift are pairwise
distinct in both coordinates as a consequence of terminal nonmerging. The
correct consequence is inequality BETWEEN the two coordinates at each aligned
time, not distinctness ACROSS different times.

The existing four-state table 0:(0,1), 1:(2,-), 2:(2,3), 3:terminal accepts
001001. Its agreeing cuts (0,3) have pair path

    (0,1), (0,2), (0,2), (1,3).

Each pair has distinct coordinates, yet (0,2) repeats. This directly refutes
that sentence. It does not refute the separate bound on nested comparable
suffix chains, or automatically refute the later single-source shape lemmas.
Their root-length/primitivity/crossing-border gap remains explicitly open.

## References and dependency scope

- [Semantic-tail proof](2026-09-08-semantic-marker-tails.md).
- [Synchronous encoding proof](2026-09-08-synchronous-separators.md).
- [Joint action/last-flag proof](2026-09-07-realizable-lastflag-spectrum.md).
- [Terminal nonmerging](2026-09-05-nonflat-overlap.md).
- [Terminal semantic transfer](2026-09-05-terminal-realization.md).
- [Unmerged strategy](https://github.com/mhenglein/subtail/blob/6b7c473efa2e6e836b872737e2d948e58098293a/notes/2026-09-08-strategy-review-and-period-state-form.md).
- [Unmerged shape lemmas](https://github.com/mhenglein/subtail/blob/6b7c473efa2e6e836b872737e2d948e58098293a/notes/2026-09-08-single-source-shape-lemmas.md).
- [Havlena et al., MFCS 2025](https://doi.org/10.4230/LIPIcs.MFCS.2025.56).
- [Freydenberger, extended regex scope](https://www.ddfy.de/publications/F-ERESaD.html).

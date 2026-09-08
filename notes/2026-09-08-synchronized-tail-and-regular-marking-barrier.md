# Synchronized semantic tails and a barrier to regular separator recovery

Date: 2026-09-08. Base main: `c4875e599958dd624dd7220dd7cbe5bb96822b11`.
Workstreams: A017 / A012; follows issue #15. No additional agents launched.

**Status: written proofs and executed independent-predicate/finite-oracle
checks. Independent mathematical review pending. Not Lean-checked. This does
not settle unrestricted Problem 1.7.** No literature-priority claim is made.

## 1. Target and reviewed baseline

The preceding main-branch contributions provide exact synchronous transition
separators and exact semantic marker-tail saturation separately. This attempt
implements their combination, removes an unnecessary all-comparison marking
constraint, and tests the intended closing argument against a stronger family.

The main baseline includes the repaired PR #12/#14 results through merged
PR #21. The remaining open PR #19 is the older repair integration; PR #16 is
the earlier explicit five-state NO certificate. Neither pending branch is
merged by this attempt. The relevant primary dependencies are:

* [synchronous-separator proof](2026-09-08-synchronous-separators.md);
* [semantic marker-tail proof](2026-09-08-semantic-marker-tails.md);
* [exact last-aligned spectrum](2026-09-07-realizable-lastflag-spectrum.md);
* [terminal nonmerging](2026-09-05-nonflat-overlap.md);
* [terminal-to-subtype transfer](2026-09-05-terminal-realization.md).

These dependencies retain their own recorded evidence levels. The new
construction does not assume the refuted sharp-profile/budget conjectures.

The hoped-for closing assertion was that encoding-aware separators plus
finite semantic tails might cover every negative terminal instance. Section 6
refutes considerably more: one fixed six-state nonflat NO instance survives
every finite tail bound after every regular, candidate-covering decoration by
separators. This includes deterministic history, regular lookahead, and
nondeterministic regular choices of markings. It does NOT refute general
existence-preserving normalization or imply subtype undecidability.

## 2. Preserve decisive comparisons, not every flagged comparison

Work first in one boundary-normalized terminal slice J: one final f, no Bad
states, no diagonal flags and no flags into f, all states reachable and
co-reachable. A proper comparison i<j<|w| is **last-aligned** if its suffixes
agree, its initial state pair is in G, and none of its positive-offset aligned
pairs is in G. Every bad word has such a comparison: choose a violation with
minimum target-suffix length.

### A smaller marking constraint graph

Use the synchronized pair graph with vertices (p,q), p!=q and p!=f.
Its endpoints are (p,f). Roots are flagged nonfinal pairs. A letter edge
follows both transitions, but is absent when either is undefined, its new
left state is f, its states merge, or its destination is flagged. Thus a
flag may be a root but cannot be entered after positive progress.
Trim to vertices reachable from roots and able to reach an endpoint.

For every retained edge labelled a from (p,q), impose

    mark(p,a) = mark(q,a).

Force each transition entering f to be marked. Union-find gives a unique
least marked set: mark the classes containing a final transition and leave
all other classes unmarked. It always exists; unlike the older strict
certificate, no cycle is forced unmarked.

This is a graph-based sufficient condition, not an exact realizability
analysis of each edge. It can still impose unnecessary equalities. Within
this constraint system the marking is pointwise minimal, so trying supersets
cannot improve any marker-count tail bound on the same comparisons.

### Exact witness-preserving compiler

Temporarily use alphabet {0,1,#}. An original transition a emits a followed
by # exactly when marked. A deterministic helper consumes # on each marked
edge. Original states retain their flags; helpers are unflagged. Every
nonempty accepted word ends in #. Erasing # recovers exactly the original
accepted run.

This presentation remains inside the binary problem: the fixed code
0->10, 1->11, #->00 gives a binary partial DFA with unflagged token helpers
and all original annotations at token boundaries. No new subtype constructor
or semantic tree label is introduced.

**Theorem 1.** For every original word w,

    Witness_J(w) iff Witness_compiled(encode(w)).

**Proof.** If the compiled word has a forbidden comparison, both endpoints
are original-state boundaries. Parsing the equal encoded fragments and erasing
# produces the original forbidden comparison. Thus an original witness cannot
be made bad by decoration.

Conversely, if w is boundary-safe and bad, take a last-aligned comparison.
Terminal nonmerging puts its pair path in the retained graph. The equalities
force the two occurrences to emit identical markers at every aligned letter,
so this comparison survives compilation. Boundary failures also survive because
all original annotations remain. This proves both directions.

The construction may erase a non-last comparison, which is harmless: some
last comparison still survives in every bad word. This is G-specific witness
preservation, not full agreement-profile equality.

In fact last-aligned comparisons themselves correspond in both directions.
Every original last comparison survives as above and has no new aligned flag
in a helper. If a compiled last comparison decoded to a non-last original
comparison, the later aligned flagged cuts would also delimit equal encoded
suffixes: they lie inside the already equal parent fragments. This contradicts
compiled last-alignment. Marker costs of decisive comparisons can therefore be
analyzed exactly on the compiled automaton.

### Strict improvement over all-pair synchronization

Take the earlier five-state all-budget NO table and its exact code 0->00,
1->10 using original state q and a shared helper 5+q for each destination.
Add flag (6,7). A comparison rooted at (6,7) advances on its mandatory zero
into the existing flag (1,2), so it cannot itself be last-aligned.

All-pair synchronization nevertheless propagates equalities from that root,
forcing a logical-one loop to be marked. Its marker spectrum is unbounded,
and the all-pair semantic wrapper returns UNKNOWN. Last-aligned marking omits
this irrelevant root continuation, obtains finite bound H=1, and proves NO.
Both compilers and the exact shared-reference search are reproduced below.
No claim is made that the original five-state NO result is new.

## 3. Exact finite marker tails with arbitrary data paths

Let K be a terminal automaton over a finite alphabet D union {#}, with every
nonempty candidate ending in #. After boundary normalization write uniquely

    w = u_0 # u_1 # ... u_(m-1) #,     u_i in D*.

For H>=0 let Tail_H(w) mean boundary safety and absence of a proper forbidden
agreement whose target suffix contains at most H markers. It is a relaxation
of Witness. H=0 is ordinary boundary-safe reachability.

**Theorem 2.** For each supplied finite H, Tail_H nonemptiness is decidable,
even with arbitrary nonflat D-paths and recurrent original flag targets.

The existing unary semantic-tail proof generalizes as follows; the implementation
makes the needed reconstruction change rather than enumerating binary words.

For H>0 retain r=min(H,m) final blocks. Enumerate their start/end/marker-successor
states. If r=H permit an arbitrary prefix of complete blocks; if r<H require
an EMPTY prefix. The latter condition is necessary for completeness of the
checked target-position set.

Choose all reference words simultaneously by reverse padded convolution.
For reference pair i<j, retain an equality bit E_ij and a persistent flag-hit
bit F_ij. A hit occurs at an equal data-tail depth. The final forbidden guard is

    F_ij and AND_{h=1,...,r-1-j} E_(i+h,j+h).

A target tail's first marker must match the source tail's first marker at the
same offset, after which the later whole blocks must match. This proves the
formula for arbitrary data words as well as unary ones. Empty data words,
empty data tails, and overlapping occurrences are included. Two different
cuts in the same data block cannot match, since their first markers occur
at different offsets.

Alongside the reference tuple keep the SET of all possible earlier-source
reverse descriptors

    (data endpoint, current state, equality mask, hit mask, finished).

On each chosen reference column, extend each active source by every legal
reverse D-edge, or finish it. Finished sources emit padding. Update masks
against the SAME reference column. This powerset describes all possible source
observations relative to one common tuple; it does not choose incompatible
reference words independently for different sources.

After every reference has finished, an unfinished longer source has an empty
equality mask and a fixed hit mask. The unmatched prefix is exactly finite
reverse D-reachability. A forward (state,pending-mask) graph then chooses a
prefix of source observations. Equality advances a pending suffix obligation;
mismatch kills it; completion rejects. At the cut, remaining obligations are
discharged against the reference equality matrix. Reference-internal guards
are checked separately. These are all the comparisons retained by Tail_H.

Reconstruct each chosen source observation by a finite reverse product against
the concrete reference tuple. Store the source state, depth capped at M+1,
equality mask and hit mask, where M is the longest reference. Once deeper than
M, no new equality/hit can appear; ordinary finite reachability suffices. This
is complete for arbitrary data alphabets. Enumerating all words up to M+k
would be unnecessarily exponential and is not the implemented recovery method.

If k is the number of states in K and c=binom(r,2), there are at most
2 k^2 4^r source descriptors and at most

    S(k,r) = (k+1)^r * 2^(2c + 2 k^2 4^r)

combined reference/powerset states. The prefix graph has at most
k*2^(r-1) states. Thus the uncapped construction terminates. Repeated combined
states can be deleted without changing the entire observation invariant; a
shortest successful convolution has fewer than S(k,r) columns. Each source
can be chosen with at most M+k data letters by shortening only its unmatched
left part. For fixed r the generous bound

    (r + k*2^(r-1)) * (S(k,r) + k + 1)

therefore suffices for a positive relaxation word. These are bounds for the
SUPPLIED-H relaxation, not unconditional witness bounds. All implementation
caps return UNKNOWN.

## 4. Composition with exact marker-spectrum analysis

For one compiled slice, each last-aligned comparison has the previously proved
form

    w=x(uv)^e u,  v nonempty,  1<=e<=k-1.

A joint finite action on single states and synchronized pairs enforces the
same u and v at every occurrence. Its accepted action templates are exact
for marked comparisons. In each template the target marker count is

    e*count_#(u) + (e-1)*count_#(v).

The action fibres are regular languages. In their Cayley graph give # edges
weight one and other edges weight zero. An SCC containing a weight-one edge
has a positive-cost cycle; all descendants have unbounded possible cost.
Zero-cost cycles do not imply unbounded marker count. For finite-cost fibres,
maximum cost is attained after removing zero-cost cycles, and is computed by
finite relaxation on the remaining graph. Retain a nonempty representative
for v even when its action is the identity and its cost is zero.

For e=1 the v coefficient is zero. Ignoring that exception would incorrectly
turn some finite target spectra into unbounded ones. For the other terms,
positive-cost Cayley lassos reconstruct actual bad words with increasing
marked target costs. Direct predicates verify those certificates.

**Corollary 3.** If the actual last-aligned marker spectrum is bounded by H,
then Witness=Tail_H on the compiled slice. Theorem 2 and decoding give an exact
YES/NO decision for every such original slice. One positive slice proves YES;
an unresolved slice prevents NO. Unbounded spectra are not negative verdicts.

This combination resolves the most recent main-branch three-state fixture

    delta=((1,0),(0,2),(-1,-1)), G={(0,1)}, final=2

with witness 01 and H=1, although the old C056 structural certificate rejects
its target-reachable separator cycle. It also reproduces NO on the ten-state
encoded five-state obstruction and the earlier six-state reset-marker NO.
It handles nonflat data inside a tail schema, not just unary runs.

## 5. A six-state nonflat NO language

Now define I with start 0, terminal final 5, no Bad states, and

    G={(0,2),(0,3),(1,2)}.

| state | 0 | 1 |
|---|---:|---:|
| 0 | 1 | 2 |
| 1 | 1 | 2 |
| 2 | 3 | undefined |
| 3 | 3 | 4 |
| 4 | 5 | 2 |
| 5 | undefined | undefined |

Its accepted language is exactly

    0^n 1 (0^(r_1)11)...(0^(r_t)11) 0^m 10,
    n>=0, t>=0, r_h>=1, m>=1.                         (A)

The productive SCC {2,3,4} contains both the zero loop at 3 and the cycle
2--0-->3--1-->4--1-->2. It is genuinely nonflat. State 1 supplies the independent
initial zero loop; no new large-state encoding is needed.

### Every accepted word is bad: an all-length symbolic certificate

Let N be the word length, n its initial zero count, m its final zero-run length
before the last 10, and j=N-m-2 the entry to that final zero run.

* If n<m, take i=0 and target N-n-2. The target starts in state 3 and equals
  0^n10, matching the initial 0^n1 followed by the mandatory first post-1 zero.
  The flag is (0,3), including n=0.
* If n=m, take i=0 and target j. The target starts in state 2 and equals
  0^m10, again matching the initial prefix. The flag is (0,2).
* If n>m, take i=n-m and target j. The source is inside the initial zeros in
  state 1; its next m+2 letters are 0^m10. The flag is (1,2).

The intervening (0^+11)* blocks are unrestricted. This proves NO for the
ENTIRE nonflat language (A), not only the two-block subfamily. It is a finite
arithmetic case partition with an arbitrary regular middle region, not a
complete certificate calculus for all inputs.

### A family with exactly one violation

For m>=1 put

    w_m = 0^(2m) 1 0^m 10.                            (B)

Its only forbidden comparison is

    i=m,  j=2m+1,  state pair (1,2),
    target suffix 0^m10, length m+2, gap m+1.           (C)

State 0 occurs only initially. Its targets in state 2 or 3 have fewer than
2m initial zeros, so its two flags cannot agree. The unique state-2 target
starts 0^m10; the only initial state-1 source matching it is i=m. This proves
uniqueness, including diagonal/empty-suffix exclusions.

Both all-pair and last-aligned graph synchronization force every defined zero
transition to be marked. This is not an unrealizable-pair artefact:

* 1010 realizes last-aligned root (0,3), whose path (0,3)--1-->(2,4)--0-->(3,5)
  equates the zero from 2 with the final zero from 4;
* w_2 realizes root (1,2) and its interior pair (1,3), equating zeros from
  1, 2 and 3;
* 01010 realizes root (0,2), equating the zero from 0 with the zero from 2.

Thus the least static marking is {(p,0):0<=p<=4}. The target in (C) then has
m+1 markers. Every finite Tail_H language is inhabited by a sufficiently large
w_m, despite the all-length NO proof. The combined solver correctly returns
UNKNOWN. The next theorem shows why adding finite marking memory is not a
complete repair.

## 6. Regular-decoration barrier: history and lookahead do not suffice

### Exact scope of the decoration model

A decoration of a binary word attaches a bit b_i to each original position.
It emits a_i followed by # iff b_i=1. Original cut-state flags are unchanged
and lifted to all auxiliary memory states; marker helpers are unflagged.
Every accepted decoration must mark its final transition, so its emitted word
ends in #. A regular decoration relation is a regular language A over
{0,1} x {0,1}; projection onto the first coordinate must cover every word in
(A). It may choose markings nondeterministically and may impose arbitrary
regular conditions on them. Restricting its projection to (A) is harmless.

For a decorated word apply Tail_H at original annotated cut boundaries; a
finite automaton for the relation can be combined with the original run, and
helper cuts carry no flags. Erasing # reflects every forbidden comparison.
The result below does not assume that every decoration preserves badness.
If a decoration erases the sole violation of w_m, it is already a survivor.

**Theorem 4 (regular-decoration barrier).** For every such finite-state
regular decoration relation A and every finite H, some decorated accepted
word survives Tail_H. More precisely, if a DFA for A has M states, put

    Q=2^M, P=M*Q.

For every m>=Q+P*(H+2), there is an A-decoration of the particular w_m in (B)
whose emitted word passes Tail_H.

The same original w_m can be chosen to survive any finite collection of such
relations and bounds, by taking m above all their displayed bounds. Hence no
finite family of candidate-covering regular decoration reductions followed by
finite semantic-tail emptiness tests is a complete NO method.

### Proof, step 1: the only comparison either disappears or forces a marker

Since erasing # reflects comparison, (C) is the only possible forbidden
comparison in any decoration of w_m. If it disappears, the decorated word is
a witness of its annotated presentation and passes every Tail_H.

Suppose it survives. Equality of its two emitted fragments forces equality
of the marking bits at every aligned original transition. Write j=2m+1 and
k=3m+2, the index of the final zero. The last aligned transition compares
original positions j and k. Since b_k=1, we have b_j=1. The first aligned
transition compares i=m and j, so

    b_i=b_j=b_k=1.                                    (D)

This ties a marker deep inside the initial zero run to the mandatory final
marker. It is independent of how the regular relation selected its bits.

### Proof, step 2: select one decoration by finite suffix viability

For the fixed original word w_m define S_t to be the set of DFA states from
which the original suffix w_m[t:] has SOME accepting bit annotation. Then
S_N is the accepting set and

    S_t = Pre_(a_t)(S_(t+1)),
    Pre_a(S)={q : delta(q,(a,0)) in S or delta(q,(a,1)) in S}.

Projection coverage ensures the initial state lies in S_0. Select the
lexicographically least accepted annotation greedily: from current DFA state
q_t choose bit 0 if delta(q_t,(a_t,0)) is in S_(t+1), otherwise choose bit 1.
This always maintains viability and produces a valid A-decoration.

This construction is a proof device, not a call to an external uniformization
theorem. Its state update may depend on future viability; it is more general
than an ordinary deterministic left-to-right marking.

### Proof, step 3: on a long zero run the joint choice is periodic

On the initial 2m zeros, S_t is an orbit of the single function Pre_0 on at
most Q subsets, read in reverse index order. Whenever at least Q zeros remain,
these subsets lie on one directed cycle of Pre_0. Moving forward through
those positions applies the uniquely determined inverse edge ON THAT CYCLE.

Thus, throughout the first 2m-Q zero positions, the pair (q_t,S_t) evolves by
one deterministic transition on at most P=M Q pairs: recover the next right
subset on its cycle, choose the greedy bit, and advance q_t. A deterministic
finite walk has preperiod at most P and period p<=P. Since m>=P, position
i=m lies in its periodic part, with at least m-Q zero positions remaining
before the right-summary cycle region ends.

If the selected decoration retained (C), equation (D) gives b_i=1. The bit 1
therefore repeats every p positions across that segment. Since
m-Q>=P*(H+2), at least H+2 of its zeros are marked. Equality of the two
fragments transfers all those markers into the target suffix in (C).
Its marker cost exceeds H, so Tail_H does not detect the sole violation.
If (C) was not retained, Step 1 already supplied the same conclusion.
This proves the theorem for every sufficiently large m, and the finite-family
corollary follows by taking a maximum. A nondeterministic A can first be
determinized; no polynomial complexity bound is asserted. QED.

### Explicit deterministic and two-sided special cases

For an N-state deterministic history marker, the initial zero transition is
a unary orbit. Once i=m>=N, b_i=1 repeats with period at most N, so choosing
m>=N*(H+1) already suffices. N can include the original DFA state; the tests
also allow the output to depend directly on that state.

For separate L-state left and R-state right summaries, output may depend on
both and on the original state. Inside the initial zero run the two summary
periods have common period at most L*R, away from the last R positions. The
same argument works for

    m >= L+R+L*R*(H+1).

These simpler bounds are tested separately. The regular-relation theorem is
stronger: the greedy selection may update its left state USING future
viability rather than reading only the prefix.

### What the theorem does not say

The original instance is decidable by Section 5's symbolic three-case argument.
Thus this is NOT an undecidability theorem for BorderAvoid or subtype entailment.
It is a counterexample to a specific completeness programme.

The projection-coverage and unchanged-flag assumptions are essential. The
result does not exclude a proved existence-preserving normalization that
discards original candidates, changes their letters or copy structure, adds
sound additional semantic constraints, or uses nonregular shared parameters.
It also does not rule out a different quantifier order that chooses a short
bad-comparison marking existentially FOR EACH word and proves that those
choices cover all candidates. Such a method needs a separate coverage proof;
it is not emptiness of the existential Tail_H search implemented here.

The literal # symbol is bookkeeping. Applying 0->10,1->11,#->00 preserves
comparison at annotated boundaries, but the cost counts logical separators,
not incidental physical zeros inside data tokens.

## 7. Implementations and executed checks

New files:

* `experiments/synchronized_tail.py`: compiler, G-specific lastflag marking,
  generic shared-reference tail search, weighted spectrum and partial decision;
* `experiments/check_synchronized_tail.py`: independent reversed predicates,
  complete finite-language oracles, analytic families and marking tests;
* `results/synchronized-tail.json`: deterministic output, seed 2026090862.

Command from the repository root:

    python3 experiments/check_synchronized_tail.py

The executed checker records:

* 1,034 complete normalized terminal table/flag cases through three states,
  131,318 raw-word checks and 7,006 defined-word compiler comparisons;
  570 YES and 464 NO. Comparison to length-six existence uses the prior
  three-state written bound, not a new claim inferred from this cutoff.
* 240 acyclic oracle inputs, of which 93 have nonempty normalized slices;
  their 201 accepted words are completely enumerated. All 372 Tail_H queries
  and exact finite marker maxima agree with independent predicates.
* 1,372 arbitrary binary-data, three-stage word-formula comparisons and seven
  infinite-language exact queries with analytic answers. These exercise
  nonflat data paths and delayed cross-block equality guards.
* 400 seeded cyclic terminal inputs: 180 YES, 217 NO and 3 UNKNOWN, with
  102,000 raw-word comparisons. This is bounded evidence, not an all-instance
  oracle. Twenty maximum certificates and six pumped certificates are directly
  checked, as are returned positive words by both existing witness predicates.
* The six-state barrier: 600 two-block exponent pairs; all 32,767 words through
  length 14, including 262 accepted/certified words; 300 longer nonflat cases
  with one to six intervening blocks; 32 unique-violation family members;
  six fully exhausted positive relaxation searches for H=1,...,6.
* All 256 memoryless edge decorations (1,024 bound checks); every two-state
  update table with 16 seeded output tables (512 checks); 120 larger-memory
  cases; all 256 pairs of two-state left/right tables with four seeded output
  tables and two bounds (2,048 lookaround checks); and 100 general regular
  decoration relations checked using exact suffix-viability selection. The
  output tables and larger relations are NOT exhaustively enumerated.
* Nine input/cap/empty-case regressions, the strict all-pair versus lastflag
  compiler example, and the latest recurrent-target fixture.

Two executions with different Python hash seeds produced byte-identical output.
The previous standalone lastflag checker was also replayed; its result remained
Git blob `1b80ca3c49f62475a4eec9a99458144e77a42563`. The unchanged dependencies
were verified as border_lab blob `1144ae52379e0417772e79582269cacd91c5bc17` and
lastflag_spectrum blob `cc2eecf4b50176dc1e128cd0238943c636fd9dd9`.

All quantified conclusions above rest on written arguments, not these counts.
No independent mathematical review, new Lean proof, full local repository CI,
or global Markdown/index validation is claimed for the partial local snapshot.

## 8. Consequence for the closing effort

The proposed combination is now implemented and resolves its advertised small
structural obstruction. The generalized regular-decoration barrier says why
iterating that combination with more finite-state separator memory is NOT a
complete closing argument. It is stronger than the previous raw-bit or
static-transition-colouring failures.

The next closing attempt should permit G-specific changes in the actual word
or a complete symbolic cover, rather than insist on preserving every candidate
by regular decoration. The six-state language supplies a concrete benchmark:
a valid cover can use the arithmetic n<m / n=m / n>m selector and leave the
intervening nonflat language symbolic. It need not encode that selector as a
finite-memory marker stream. A general theorem still needs effective coverage,
shared-assignment soundness, and all-input termination. This attempt supplies
neither a general cover nor an undecidability reduction.

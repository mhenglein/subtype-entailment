# Last-target anchoring and a certified recurrent decision class

Date: 2026-09-13. Base: `c4f7e56665828710b3bda77e32bb2904ad4006d6`.
Workstreams A017/A008; claims C077-C078; experiment E050.

**Status: written proof plus executed reproducible checks. Independent mathematical
review pending; not Lean-checked. This does not decide unrestricted Problem 1.7.**

The result is a complete native algorithm for a precisely certified class with
multiple recurrent sources and targets. It is not another supplied power scheme
or a claim that a larger finite search cutoff must suffice. A quadratic witness
bound is proved for the class. On arbitrary inputs the wrapper remains partial:
failed certification returns UNKNOWN, never NO.

## 1. Exact setting and prior dependencies

An instance is a finite partial deterministic automaton I=(Q,delta,s,F,G,Bad)
over a finite alphabet. The original subtype application uses alphabet {0,1}.
All finals are terminal: they have no defined outgoing transitions. On a defined
run of w of length n, write c(i) for the state at cut i, including both endpoints.
A witness is a safe accepted word for which, at every i<=j,

    w[i:i+n-j] = w[j:n]  implies  (c(i),c(j)) not in G.

The diagonal i=j and the empty suffix j=n are included.

For each selected final f, delete Bad states, states with diagonal flags, and
sources p of flags (p,f). Trim to states reachable from s and able to reach f.
Other terminal finals cannot be on this slice. Delete flags outside the slice,
flags sourced at f, and the now-irrelevant boundary pairs, then densely relabel.
An empty slice is NO. A terminal initial state accepts only epsilon and is handled
directly. This is the existing boundary normalization, not a new semantic rule.
All later constructions concern a nonempty normalized single-final slice with
k states, no Bad, no diagonal flags and no final-column or final-source flags.

C036 proves terminal nonmerging: two proper agreeing suffix occurrences cannot
have the same state at any aligned position. Otherwise their common future
would make the earlier run enter a terminal final before the word ends. The
period lemma below is another form of the terminal periodicity mechanism in
C038, not a priority claim for that mechanism. The static synchronization in
Section 5 builds on the last-aligned transition equalities in the September 8
synchronized-tail note. Those dependencies keep their recorded proof levels.
The new argument is given explicitly so that its scope can be audited without
trusting an imported implementation.

## 2. All targets collapse to the last one for complete columns (C077)

Let T be a subset of nonfinal states. Suppose the ordered flags are exactly

    G_T = {(p,t) : t in T, p != t, p != f}.

A target has every possible proper nonfinal source flagged. Excluding p=t is
essential: including those diagonal flags would prohibit visiting T altogether.
Terminal nonmerging already excludes proper matches from equal states.

**Last-target lemma.** If an accepted word w never visits T, it is a witness.
Otherwise let j be its last T-labelled cut and Y=w[j:n]. Then

    w is a witness  iff  Y has no occurrence starting before j in w.

**Proof.** Y is nonempty since f is not a target. An earlier occurrence at i<j
has c(i)!=c(j) by terminal nonmerging and c(i)!=f because the run continues.
Consequently its pair belongs to G_T, so w is bad.

Conversely, suppose a proper forbidden comparison starts at i and targets a
cut j0<=j. Its target suffix w[j0:n] ends with Y. Its equal earlier copy contains
Y starting at i+(j-j0)<j. Thus absence of an earlier Y rules out all proper
comparisons, including those at every earlier recurrent target. The normalized
slice already excludes diagonal and empty-suffix failures. QED.

The sufficient direction does not need complete columns: **for arbitrary G, a
unique suffix at the last occurrence of any G-target is enough for witnesshood**.
This yields the all-input positive test in Section 3. Necessity requires the
complete-column hypothesis or the separately certified replacement in Section 5.

Equivalently, write Y=Za and w=XZa with a a final letter. Then the one required
condition is

    Za is NOT a contiguous factor of XZ.                         (1)

The language of prefixes X from s to the chosen t is regular. The language of
tails Za from t to f having no positive T cut is regular. For each fixed t,a,
this gives independent regular constraints on X and Z and exactly one negated
containment atom. The same Z occurs on both sides; it is not independently
chosen. The implemented formula compiler retains this alternative formulation.
It is not used as an unimplemented oracle by the native algorithm below.

## 3. A productive last-target tail cycle proves YES, for arbitrary flags

**Terminal period lemma.** If a word Y accepted by a k-state terminal DFA is a
prefix of an infinite word of period d>=1, then |Y|<k*d.

**Proof.** Consider the |Y|+1 pairs (state after i letters, i modulo d). If
|Y|>=k*d, two pairs repeat, at i<j. Periodicity makes the remaining input from j
identical to the corresponding input from i. Determinism therefore reaches the
same final at cut |Y|-(j-i), strictly before |Y|. A terminal final cannot continue
to the actual endpoint, contradiction. Hence all these state/phase pairs are
distinct, implying |Y|+1<=k*d. QED.

For a target t, let L_t be the language of paths from t to f that never visit T
at any positive cut. Its initial t is permitted once; all transitions entering
T are forbidden. Infinitude of L_t is decided by a productive cycle in this
finite graph. A cycle disconnected from t or from f does not qualify.

Suppose L_t is infinite. Choose a shortest path X from s to t, with m=|X|<=k-1.
Choose an accepted tail Y in L_t of length at least k*m. Such a Y exists because
L_t is infinite. One can choose

    k*m <= |Y| <= k*m+k-1:                            (2)

take the first k*m letters of any sufficiently long path and follow a shortest
allowed continuation from the reached state to f. When m=0, any shortest tail
suffices instead. All states of the concatenation remain boundary-safe.

If Y occurred earlier in XY, its start would be inside X. The shift d between
that occurrence and the terminal one satisfies 1<=d<=m. For m>0, |Y|>=k*m>=d,
so the occurrences overlap and Y has period d. The period lemma gives
|Y|<k*d<=k*m, contradiction. If m=0 there is no earlier cut at all. Therefore
Y is unique, and XY is a witness even for arbitrary sparse G.

The entire witness satisfies

    |XY| <= (k+1)m+k-1 <= k^2+k-2.                    (3)

This is a sound positive certificate with no flag-completion assumption. If no
qualifying cycle exists, that failure is UNKNOWN for arbitrary inputs, not NO.
A target-free whole accepting path is another immediate positive certificate.

The implementation finds Y by finite BFS on (state,min(length,k*m)). This is an
explicit terminating graph construction, not iteration until a lucky word appears.

## 4. Complete native decision and quadratic witness bound (C077)

Now impose the complete-column hypothesis from Section 2.

First search for a target-free accepting path. Next analyze each L_t. Any
infinite L_t gives YES by Section 3. If L_t is finite, its productive graph is
acyclic, so every tail Y in it has length at most k-1. Enumerate ALL these tails;
there may be exponentially many, but there are finitely many by this proof.
A supplied length cutoff is not being substituted for graph finiteness.

For each fixed nonempty Y, build the pattern-avoidance DFA K_Y with |Y| states.
Its state is the length of the longest suffix of the word read so far which is
a proper prefix of Y. A transition completing Y rejects. This is the usual
finite failure-function construction; its complete table is constructed by code.
Let A_Y be the states of K_Y from which reading Y without its last letter does
not reject. Search the product graph Q x K_Y from (s,0) for (t,q), q in A_Y.

A path in that product spells exactly an X reaching t for which Y does not
occur in X Y[:-1]. Thus (1) holds and X Y is a witness. Conversely, every witness
having this last-target tail provides such a product path. Exhausting the entire
finite graph proves that no suitable X of ANY length exists for this Y.

If the product succeeds, a shortest successful X has length at most k*|Y|-1.
The resulting word has length at most

    (k+1)|Y|-1 <= (k+1)(k-1)-1 = k^2-2.

Combine this with (3), the target-free case, and the direct epsilon case:

**Theorem C077.** Complete-target-column terminal instances have a complete
native decision algorithm. Every positive k-state instance has a witness of
length at most k^2+k-2 for k>=2; k=1 is handled directly with length zero.
The bound is not claimed sharp. No power-scheme or source-visit bound is assumed.
Existence for this class has an NP upper bound, by guessing the bounded word
and checking the original cut-pair predicate. No hardness claim is made.

The implemented tail enumerator may retain exponentially many finite tails;
no polynomial-space claim is made for that implementation. The positive word
bound and NP upper bound do not imply polynomial deterministic running time.
For negative answers the saved certificate lists every tail and the full
reachable prefix-product set. The separate replay verifies finite tail coverage,
closure and absence of success using literal suffix operations, not KMP.

The finite-tail branch overlaps C037's acyclic last-flag regime. The productive
cycle branch, direct quadratic bound and full last-target characterization are
recorded explicitly here; no claim is made that every fixture evades all earlier
restricted solvers. Multiple recurrent sources/targets alone are not a novelty
criterion or evidence of unrestricted completeness.

## 5. A polynomial finite-graph certificate for sparse G (C078)

This section supplies an automatic sufficient test on the ORIGINAL input, rather
than asking a user to supply a scheme, delimiter structure or reference word.
It retains the same states and one output token per original letter.

### 5.1 Last-aligned comparison graph and finest static coloring

A proper forbidden comparison is last-aligned when none of its positive-offset
aligned pairs is flagged. Every bad normalized word has one: choose a violation
with minimum target-suffix length. Terminal nonmerging puts it in the following
graph. Vertices are (p,q) with p!=q and p!=f. A letter a advances both coordinates
when both transitions exist, the new left state is not f, the new coordinates
are distinct and the destination pair is NOT in G. Roots are G and endpoints
are (p,f), p!=f. Trim to vertices reachable from roots and able to reach endpoints.

For every retained edge out of (p,q) on original letter a, impose equality
between transition colors color(p,a) and color(q,a). Union-find on defined
transition occurrences supplies the finest partition satisfying all equalities.
Distinct original letters never share a class. Assign one new token to each class.
There are at most 2k tokens for a binary original input. A token still has a
well-defined underlying original bit, and outgoing transitions stay deterministic.

The last-aligned synchronization principle is prior September 8 work. Here it
is used to distinguish transition letters maximally, rather than add separators.

**Coloring lemma.** Original words and colored accepted words correspond
bijectively, with the same length and state run, and witnesshood under the SAME G
is preserved in both directions.

Proof: decode a colored token to its underlying original letter. Any colored
comparison becomes a raw comparison, so coloring cannot make an original witness
bad. Conversely, every bad original word has a last-aligned comparison; every
one of its aligned edges is retained in the graph and receives equal colors.
That comparison survives. Boundary exclusions are unchanged. QED.

### 5.2 Certify column completion without introducing spurious violations

Let T be the targets of G. In the colored synchronized graph, search for a path
to an endpoint (p,f) that avoids G at EVERY vertex, including its root. Its root
may be any unflagged (p,t) with t in T, p!=t, p!=f, and t reachable from p in the
original graph. The reachability condition is necessary for cuts occurring in
that order; it is deliberately only a coarse occurrence condition.

If no such path exists, return CERTIFIED. Otherwise return UNKNOWN with the
finite synchronized path. That path need not itself be realizable as two cuts
of one word, and it is never a NO certificate for witness existence.

**Column-completion lemma.** When the test passes, replacing G by G_T in the
colored automaton preserves witnesshood exactly.

Proof: G subseteq G_T gives one implication. For the other, take a proper
colored comparison into any target t. If its root is in G it is already bad.
Otherwise follow the aligned pairs. If any later pair is in G, that pair gives
a genuine later forbidden comparison on the same word. If none is in G, the
whole comparison is a forbidden root-to-end path of the finite certificate
search, contradicting its successful exhaustion. Root occurrence order supplies
the coarse reachability premise. QED.

**Theorem C078.** A normalized slice passing this finite certificate is decided
by coloring, completing target columns and applying C077. Both transformations
preserve the state count and word length. Hence every positive certified slice
has an ORIGINAL witness of length at most k^2+k-2. The certificate construction
is polynomial in the explicit original table and flag relation. The colored
alphabet is an internal finite representation; no subtype constructor or type
semantics is changed. Returned words are decoded and checked in the original
binary instance by both direct predicates.

For multiple finals, analyze the boundary slices separately. Any YES slice
proves nonempty witness language. Return NO only if every slice is empty or
certified NO. An uncertified nonempty slice prevents a global NO. The independent
positive test from Section 3 can additionally succeed even when coloring fails.

Within this static synchronization discipline the coloring is finest. Coarsening
it cannot remove a synchronized obstruction that already has equal colors.
This does not claim anything about richer history-dependent transformations,
flag rewrites, changes of word, or more general existence-preserving covers.

## 6. Explicit scope tests

The fixture `recurrent_yes` has six states and returns the binary word 0110.
The seven-state fixture `recurrent_no` has an exact native NO. Each has at least
two source states and two target states in one nonflat strongly connected
component, and neither original flag relation is a complete-column relation.
The full JSON records their tables, flags, colors and certificates.

The NO fixture's only last-target tail is a single colored symbol. Its prefix
avoidance certificate has four reachable product states and is closed with no
successful exit. No assertion that accepted words were all enumerated up to a
convenient bound is needed to replay its NO.

The eight-state `sparse_cycle_yes` fails the coloring certificate but has a
productive target-free tail after a reachable target. The general positive
lemma returns an 18-letter original witness, within the proved bound.

Two decisive negative scope tests are retained:

* The existing six-state regular-marking barrier is mathematically NO by its
  earlier arithmetic proof, but this wrapper returns UNKNOWN. Its synchronized
  obstruction is not promoted to nonexistence.
* The existing eight-state (2,3)-period modular family is positive with witness
  `(1^6 0)^2`, but returns UNKNOWN. Its colored last-target suffix repeats, so
  forcing column completion without the certificate would erase a valid witness.

Thus the certificate is not a characterization of all YES or all NO instances.
C073/C076 and Q004 are untouched. A general effective reduction to an anchorable
class, potentially with state growth or a different representation, remains an
unproved obligation, not a conclusion from these examples.

## 7. Literature route and its boundary

The initial route outline considered Havlena, Hecko, Holik and Lengal,
*Negated String Containment Is Decidable*, MFCS 2025, Theorem 28,
DOI 10.4230/LIPIcs.MFCS.2025.56. Its single-negated-containment problem allows
concatenations of shared variables with independent regular constraints. For
(1), use needle Za and haystack XZ, treating a as a variable constrained to a
singleton language. This is an exact one-atom mapping, not a claim about arbitrary
conjunctions of negated containments or about different transduced copies of X.
The paper's notation places the needle first; the implementation uses explicit
`needle`/`haystack` fields to avoid an argument-order ambiguity.

The subsequent terminal-period argument gives the self-contained native
algorithm above and its stronger specialized bound. **No decision theorem from
that paper is needed for C077 or C078.** No complete external string backend,
multiple-not-contains theorem, or generic quantifier-elimination procedure was
implemented or assumed.

## 8. Reproduction, evidence levels and remaining question

Run from the repository root, with Python 3.10+ and assertions enabled:

    python3 experiments/check_target_anchor.py --output /tmp/target-anchor.json --full-output /tmp/target-anchor-full.json
    cmp results/target-anchor.json /tmp/target-anchor.json
    python3 experiments/target_anchor.py --fixture recurrent_no --certificate-output /tmp/target-anchor-no.json
    python3 experiments/target_anchor.py --fixture recurrent_yes
    python3 experiments/target_anchor.py --fixture modular_positive_unknown

The full output reconstructs the colored tables, witness words and finite
negative proofs. The committed compact output records seeds and counts. The
suite includes all 1,024 partial three-state terminal tables/proper-flag sets,
588 complete class-bound oracles, 150 complete acyclic languages, 40,640 boundary
word comparisons, 6,765 larger sparse coloring comparisons, 31,682 KMP/literal
comparisons, 5,400 periodic-prefix cases and 58 negative certificate replays.
An intentionally corrupted negative certificate is rejected.

Counts are implementation evidence, not an independent mathematical referee.
The all-length statements rely on the ordinary proofs in Sections 2-5. No
Lean proof, unrestricted decision or independent re-certification of the entire
subtype-to-terminal bridge is claimed. When applying the result to subtype
entailment, C030/C031 retain their existing status and arbitrary-tree semantics.

The specific remaining global question is whether arbitrary safe flagged
comparisons can be organized into an effectively controlled collection of
anchors without losing the shared candidate word. A static single-anchor
completion is now decidable and tested, but the modular positive counterexample
shows why simply completing every target column is not that theorem.

# Counter lifts for repeated-source walk schemes

Date: 2026-09-12. Research base: `52d5270342b27aee3cad10e1b2d0ac7d9307a580` of `mhenglein/subtail`.

**Status: written proof and executable finite regressions. No independent mathematical review or Lean verification. No unrestricted subtype-entailment decision procedure is claimed. The remote repository has not been modified.**

## Result in one paragraph

The repository's C071 eliminates the unbounded collection of source-boundary comparisons in a power of an unknown first-return word. C072 uses that primitive for supplied source-simple cycle schemes. A finite counter lift removes the source-simple restriction: a supplied base walk may revisit the same source state, provided its finite source walk is part of the input. Every repeated source occurrence becomes a distinct first-return pivot in a suitable counter lift. Different phases use separate counters but keep all their word variables and tails shared. This gives an exact positive existential word-equation reduction for a supplied finite closed-source-walk power scheme, and therefore a PSPACE upper bound using the same external theorem. Neither the number of phases nor the lengths of the supplied walks are bounded from an arbitrary instance here.

The lift and the compilation extension below are the contribution of this continuation. C071's capture/conjugacy argument is an existing dependency, not a new result or a newly formalized theorem. No literature-priority claim is made.

## 1. Exact semantics

An instance is

`I = (Q, {0,1}, delta, q0, F, Bad, G)`,

where Q is finite, delta is a partial deterministic transition function, every final state in F has no outgoing transitions, Bad is a set of forbidden states, and G is an ordered relation on Q. A safe run visits no Bad state, including at its initial and final positions. Undefined transitions reject.

For a word w with safe accepted run c(0),...,c(n), witnesshood means

    for every 0 <= i <= j <= n,
        w[j:] is a prefix of w[i:]
        implies (c(i),c(j)) not in G.

Diagonal comparisons and the empty suffix are included. These are finite witness words in the repository's reduction; the original subtype assignments are still arbitrary, possibly infinite trees. Nothing below replaces arbitrary-tree semantics with finite-tree semantics.

Let

    S = {p in Q : some (p,t) belongs to G}.

A source visit is a run position, not a distinct state label.

For a safe path w from p, and a counted set T subset Q, define the arrival count

    a_T(p,w) = number of i with 1 <= i <= |w| and delta(p,w[:i]) in T.

This count EXCLUDES the initial position. For a loop at a counted pivot it INCLUDES the returning endpoint. This convention is essential: it makes arrival counts additive on concatenated paths.

## 2. The exact counter lift

Fix a positive integer d. The T-counter lift has states

    Q x Z/dZ.

Its transition rule is

    delta_d((q,r),a) = (delta(q,a), r + [delta(q,a) in T] mod d)

when the original transition is defined, and is undefined otherwise. Its start is (q0,0). Its final and Bad sets are the full products of F and Bad with Z/dZ. Its flags are

    ((p,r),(t,s)) in G_d  iff  (p,t) in G,

for ALL residues r,s. It has k*d states and |G|*d^2 flags before any optimization.

### Lemma 1: exact projection

For every initial state p, initial residue r, and finite word w, the lifted run exists and is safe exactly when the original run from p exists and is safe. Whenever defined, its state at position i is

    (c(i), r + a_T(p,w[:i]) mod d).

Acceptance is preserved. Witnesshood is preserved in both directions.

**Proof.** Induction on i gives the displayed run formula. Bad and final membership depend only on the first coordinate. The bit word does not change, so every suffix-prefix equality is the same equality before and after lifting. The lifted flag definition tests exactly the original ordered state pair, regardless of either residue. Thus every forbidden comparison is preserved, including diagonal and empty-suffix cases. QED.

It would be incorrect to lift only equal-residue flags. That would erase original comparisons whose endpoints have different counter values.

### Lemma 2: any supplied-count loop becomes first-return

Suppose p belongs to T, B is a nonempty safe p-loop, and

    d = a_T(p,B).

Then d is positive, and B is a first-return word at (p,0) in the d-counter lift: it returns there at its end and nowhere strictly inside.

**Proof.** The endpoint has residue d mod d = 0. At any strictly internal occurrence of p, at least one counted arrival has occurred. The final return to p is another counted arrival, still ahead. Therefore the current arrival count lies between 1 and d-1, so that occurrence cannot carry residue zero. An internal occurrence of any different original state cannot equal (p,0) either. QED.

The lemma does not require B to be lexically primitive. It also does not require B to be first-return in the original graph.

### Lemma 3: rotations retain the same arrival count

Split B = P C at any source position of the loop, carrying state s in T. The rotated word R = C P is a safe s-loop with d counted arrivals. Consequently it first-returns at (s,0) in the d-counter lift.

**Proof.** The rotation traverses the same cyclic run edges in cyclic order. The endpoint destinations on those edges are the same multiset, including counted states with their multiplicities. Its count is therefore d. Apply Lemma 2 at s. QED.

## 3. Exact powers without a primitivity assumption

A raw commuting-word equation is insufficient to express that U is an integral number of copies of B. For example B=1010 and U=10 commute, but U is not in B*.

### Lemma 4: arrival-count guarded powers

Under Lemma 2's hypotheses, for every finite U,

    UB = BU,
    U is a safe loop at p,
    a_T(p,U) == 0 mod d

hold together if and only if U=B^m for some integer m>=0.

**Proof via the lift.** The regular path condition is precisely that U loops at (p,0) in the d-counter lift. Lemma 2 makes B first-return there. For a first-return loop B, the commuting-loop condition admits exactly B*: commuting nonempty words have a common primitive root x, say B=x^a and U=x^b. Under the action of x, the pivot returns periodically, with a least positive return exponent a0. Every return exponent is a multiple of a0. If a0<a, B would visit its lifted pivot strictly internally. Hence a=a0, and a divides b. The empty U gives m=0. The converse follows by concatenating complete lifted B-loops. QED.

For completeness, the common-root fact can be proved by cancellation induction: if nonempty X,Y commute and |X|<=|Y|, equality XY=YX makes X a prefix of Y. Write Y=XZ and cancel to obtain XZ=ZX. Induct on the sum of lengths, with empty/equal cases immediate. The two words are powers of a common word, which can then be reduced to its primitive root.

There is also a direct count proof. In the original automaton let a0 be the least root-action return exponent, and put C=x^a0. Then B=C^u, U=C^v, and h=a_T(p,C)>0. The divisibility guard says u*h divides v*h, hence u divides v. Again U is a whole B-power.

### Why this is a word-equation/regular construction

For FIXED supplied d, the two non-equational conditions in Lemma 4 are a single finite-DFA membership constraint for U. No integer-valued length variable, multiplication predicate, primitivity predicate, or variable modulus is inserted into the word-equation logic.

The exact count of B is enforced by the supplied source walk in the next section. A modulus inferred from an unknown, unbounded B cannot simply be installed in a finite input automaton. That is outside the construction.

## 4. Supplied closed-source-walk schemes

A scheme has a supplied finite sequence of phases. Each phase has a source pivot. A phase is either plain or powered.

For a powered phase at pivot p, supply a nonempty finite list

    s0,s1,...,s_(d-1), with s0=p and every sj in S.

The list MAY REPEAT STATES. Put s_d=s0. Introduce unknown positive path words

    A_j : s_j -> s_(j+1)

whose interiors contain no source. These are explicit regular path languages. Their concatenation

    B=A_0 ... A_(d-1)

is a safe nonempty p-loop with exactly d source arrivals. The list specifies source positions in one base, excluding its returning endpoint, not distinct source labels.

The phase contributes U=B^m with m>=1, or contributes U=epsilon as an empty-star branch. The empty branch does not require any base or segment word to exist. A plain phase contributes epsilon and has no base.

With h phases, the whole word is

    W = C_0 U_0 C_1 U_1 ... C_(h-1) U_(h-1) C_h.

C_0 is a safe path from the original start to its first source, the first pivot. Each intermediate C_i is a positive path between the adjacent pivots with no interior source. C_h safely accepts from the last pivot with no positive later source visit. All these are regular languages. A scheme with no phases means a safe accepted path avoiding all sources. Empty accepted words and terminal source pivots are allowed when the corresponding path conditions permit them.

All choices of segment words, base words, powers and bridges belong to ONE assignment. In particular, the suffix after phase i is the shared word

    Y_i = C_(i+1) U_(i+1) ... U_(h-1) C_h.

It is not chosen independently for different source obligations.

### Explicit path DFAs

For a positive next-source path from p to q, use a fresh initial copy of p. The original source states have no outgoing edges. Only q is accepting, and transitions entering other source states are removed. The fresh copy retains p's original safe outgoing edges. This enforces positivity even when p=q.

For entry, stop at the designated first source and reject visits to other sources. For exit, delete all transitions into any source, but retain the initial pivot. Bad states and incident transitions are removed in each construction. Each such DFA uses at most k+1 states.

## 5. Eliminate all comparisons inside a powered walk

We use the repository's C071 primitive in its exact recorded scope:

> Given a terminal instance, an unknown nonempty first-return word R at a pivot, a word V=R^m, and an accepted tail Z, a finite positive existential formula checks all forbidden comparisons sourced at the displayed R-boundaries of VZ. Targets may occur anywhere later. The number m and word lengths are unbounded.

That primitive uses unique terminal accepted-prefix captures and the full three-case power-conjugacy calculation. It is not an earliest-boundary-only approximation. Its proof and the exceptional-conjugacy regression remain dependencies.

Consider one active generalized phase with base B and walk length d. Use the S-counter lift modulo d only for this phase. Lemma 4 expresses U=B^m by

    UB=BU and U in the lifted pivot-loop language,

with U nonempty in the active branch.

For every occurrence j in the supplied walk, define

    P_j = A_0 ... A_(j-1),
    Q_j = A_j ... A_(d-1),
    R_j = Q_j P_j.

Introduce V_j by the equation

    U = P_j V_j Q_j.

Since B=P_j Q_j and U=B^m, cancellation gives uniquely

    V_j = (Q_j P_j)^(m-1) = R_j^(m-1).

By Lemma 3, R_j first-returns at (s_j,0) in the lift. Invoke C071 with

    pivot = (s_j,0),
    base = R_j,
    power = V_j,
    tail = Q_j Y_i.

The displayed boundaries are exactly the copies of that particular source OCCURRENCE inside the phase. In particular, two occurrences of the same original source label are treated separately. Every internal source position of every copied base is covered by one such invocation.

The phase-exit pivot, at the start of Y_i, is checked separately using C067's fixed-source capture formula. Bridges have no interior source positions, so no source obligation is lost there.

### Theorem 5: exact compilation for generalized supplied schemes

Using C071, the resulting finite positive existential formula is satisfiable if and only if the supplied closed-source-walk power scheme contains a witness of I.

**Soundness.** The entry/bridge/exit and segment constraints give one safe accepted run. Each active phase is an integral whole-base power by Lemma 4. C071 at its rotations checks every source occurrence inside that phase. The fixed-source exit clauses check the phase pivots after the powers. The source-position partition is exhaustive. Every lifted comparison is exactly the original comparison by Lemma 1. Thus the assembled word has no forbidden comparison.

**Completeness.** Take a witnessing member of the supplied scheme, including its chosen phase decomposition. Use its actual segment, base, power, bridge and suffix words for the primary variables. For each active phase use its actual rotations and powers R_j^(m-1). Lemmas 2-3 supply the required first-return conditions. Projection makes every applicable C071 condition true, and C071's completeness supplies its auxiliary words. Assign fresh variables in unused disjuncts arbitrarily. All clauses share the original chosen words, so they hold simultaneously. QED.

### Different phase lengths do not require a common counter

For phase lengths d_0,...,d_(h-1), each invocation uses its own k*d_i-state lift. Finite automata appearing in one word-equation formula may have different state sets and start states. They nevertheless test the SAME word variables. There is no need to take the least common multiple or product of all moduli, and no permission to give separate values to the common tails.

This is important both for exactness and for the polynomial-size bound.

## 6. Decision-theoretic consequence and exact external theorem

For an explicitly supplied scheme, the output formula has size polynomial in the instance and the explicit walk lists. Each local lift has k*d_i states; lifted flags are quadratic in d_i; each occurrence generates one C071 call; the C071 formula with finite-DFA atoms is polynomial in its input automaton. The word terms and shared tails have polynomial total size as well. Replacing membership of a composite term T by fresh X=T and X in L keeps membership atoms variable-only with polynomial growth.

The external result is Theorem 4, printed page 8, in:

Volker Diekert, Claudio Gutierrez and Christian Hagenah, *The existential theory of equations with rational constraints in free groups is PSPACE-complete*, arXiv:cs/0103018v1 (2001).

Despite the title, Theorem 4 specifically concerns closed existential propositional formulas of word equations and regular constraints in free MONOIDS with involution. The primary PDF's theorem statement and preceding definition were inspected in this continuation. The entire external proof was not re-proved here.

Apply the involution-free fragment: constants and variables use binary finite words, terms use only concatenation, and regular languages are supplied by explicit finite automata. Alternatively use an extended involution alphabet and constrain every used variable to {0,1}*. No group cancellation, universal quantifier, general arithmetic constraint, or implicit unbounded operator is involved.

Therefore witness existence INSIDE A SUPPLIED generalized scheme is decidable and lies in PSPACE. This is an upper bound only; no hardness result for this scheme format is claimed. The implementation below is a formula compiler, not an implementation of the full decision algorithm.

A supplied bound on the number of phases and their total explicit source-walk length also yields a decision by enumerating or guessing the finitely many schemes within that bound. A unary-encoded total size bound preserves a PSPACE upper bound in that augmented input size. An unrestricted computable bound is not obtained.

## 7. Concrete checks against two unsafe shortcuts

### Fractional commuting powers

Use start 0, terminal final 3, Bad empty, flag (0,2), and table

    0: 0->0, 1->1
    1: 0->0, 1->2
    2: 0->3, 1->undefined
    3: both undefined.

The source set is {0}. For the supplied walk (0,0), B=1010 has two source arrivals. U=10 commutes with B and is a safe loop at 0, but has only one arrival and is not a B-power. The modulo-two loop condition rejects it.

For comparison, U=B and Y=110 give the genuine witness 1010110. The flag is not dead: accepted word 0110 has an actual (0,2) comparison.

### Interior source-loop deletion can fail even with one flag

Use start 1, final 4, Bad empty, G={(1,0)}, and table

    0: (0,1)
    1: (3,undefined)
    2: (0,4)
    3: (2,0)
    4: (undefined,undefined).

The word w=01001011001 is a witness, with run

    1,3,0,0,0,1,3,0,1,3,2,4.

Deleting the loop on letter interval [5,8), namely 011, leaves

    v=01001001,
    run 1,3,0,0,0,1,3,2,4.

It remains accepted. But at cuts (0,3), v[3:]=01001 is a prefix of v, and the endpoint-state pair is (1,0). Thus v is not a witness.

This refutes arbitrary interior source-loop deletion. It does NOT refute the existing single-source FIRST-TO-LAST normalization: that is a different deletion with no earlier protected source left behind. No global minimality claim is made for this example. The local minimization only checked shorter words for this fixed table.

## 8. Implementation and evidence

`closed_walk_lift.py` implements the lift, arrival-count guard, explicit DFAs, C071 expansion, and generalized scheme compiler. The JSON formula contains only equality, regular membership, finite conjunction/disjunction, and a single existential variable block. Non-suffix tests are expanded into positive word equations. The separate evaluator evaluates a supplied assignment; it is not a satisfiability solver.

`check_closed_walk_lift.py` uses seed 2026091217. Recorded checks include:

- 22,950 word-level projection comparisons on 90 generated terminal instances, all binary words through length 7, states 2..6 and moduli 1..4.
- 39,346 guarded-power comparisons, including 1,605 commuting non-powers rejected by the count guard; 4,925 rotated first-return checks.
- 550 complete phase queries and 1,228 lifted-boundary queries against direct suffix comparisons and a separately written reversed-border predicate.
- 225 explicit non-suffix assignments, 100 boundary-formula assignments, and 20 full-scheme assignments. There were 65 satisfying boundary assignments and 8 satisfying full-scheme assignments; the remaining recorded assignments evaluated false.
- 9 multi-source full-scheme assignments; 9 shared-tail multi-phase assignments with different local counter sizes; 2 empty-star cases whose prescribed base language is empty.
- Both counterexamples above and the repository's exceptional-conjugacy regression 010010101.

A false auxiliary assignment is NOT a proof of formula unsatisfiability. The experiment explicitly labels these as false assignments, not UNSAT results. The compiler's all-length equivalence and the decidability conclusion rely on the written argument and its C071/external-theorem dependencies. Successful assignments are concrete positive certificates checked against the serialized Boolean formula, its DFA membership constraints, and the original witness predicates.

The example formula has 1,935 syntax nodes, 564 equations, 689 regular atoms, 676 existential word variables, and 49 distinct DFAs with 824 states in total. No compressed powers or opaque capture operators remain in that serialized formula. These size counts concern the example, not a complexity lower bound.

No native SMT solver, general word-equation decision procedure, Lean build, full repository CI, or independent mathematical referee was used in this continuation. The core all-length claims have written-proof status only.

## 9. The exact remaining completeness obligation

Define scheme cost as the number of phases plus the total number of source positions listed in their powered bases. Copy exponents and the lengths of source-free path words are not counted.

A sufficient closing theorem would be a total computable H(k) such that every positive k-state terminal instance has SOME witness in a scheme of cost at most H(k). Theorem 5 would then decide each of the finitely many schemes in that bound. Such a theorem must preserve existence, not every original candidate or complete comparison profile.

No such bound is proved here. A path may change its return words and source walk without an established bound on the number or complexity of the resulting phases. The counter lift handles repeated labels in a supplied base, but its modulus is the supplied base's finite source-arrival count; it does not bound that count from k.

Every finite witness can be described by a finite plain-visit scheme, so enumerating more schemes is a positive semidecision procedure. It does not give a stopping condition on negative inputs. Finiteness of the set of k-state instances also does not make their witness/scheme maxima computable.

The earlier superpolynomial lower bound on TOTAL source visits does not refute a small scheme-cost bound: a short symbolic phase can represent arbitrarily many visits. Conversely, handling such visits symbolically does not prove that finitely many phases suffice for every positive input.

The next discriminating target is therefore an existence-preserving bound or complete symbolic treatment for changing return words and changing source walks, with earlier shared-tail obligations preserved. The interior-deletion example in Section 7 remains a mandatory regression. No undecidability reduction is established by either that obstruction or by failure of a particular cover.

## Sources and provenance

Repository revision: `52d5270342b27aee3cad10e1b2d0ac7d9307a580`.

- [Repository state at the research base](https://github.com/mhenglein/subtail/blob/52d5270342b27aee3cad10e1b2d0ac7d9307a580/STATE.md).
- [C071/C072 source-power proof](https://github.com/mhenglein/subtail/blob/52d5270342b27aee3cad10e1b2d0ac7d9307a580/notes/2026-09-10-source-power-schemes.md).
- [C067/C068 source-capture proof](https://github.com/mhenglein/subtail/blob/52d5270342b27aee3cad10e1b2d0ac7d9307a580/notes/2026-09-09-source-capture-word-equations.md).
- [Q004](https://github.com/mhenglein/subtail/blob/52d5270342b27aee3cad10e1b2d0ac7d9307a580/research/conjectures/Q004.md).
- [Diekert--Gutierrez--Hagenah 2001, Theorem 4](https://arxiv.org/pdf/cs/0103018), printed page 8.

The repository's subtype bridge and the existing C071 proof retain their recorded evidence levels. This note does not allocate repository C/E/Q identifiers, change the canonical research tracker, or claim to supersede concurrent work.

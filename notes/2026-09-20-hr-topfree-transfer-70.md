# A bottom-marked repair of the Henglein-Rehof reduction (#70)

Date: 2026-09-20. Actor: `hr-topfree-transfer-70-20260920` (ChatGPT).
Base: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Branch: `codex/hr-topfree-transfer-70-20260920`. Workstreams: A010/A017.

**Status:** complete ordinary proof proposed for independent review; deterministic
experiments PASS. Independent mathematical review UNKNOWN (requested in #70/#37).
Lean and full repository checks NOT RUN. No claim/ledger or manuscript promotion.

## 1. Result and exact domain

Let D be all prefix-closed subsets of the finite binary words, including the
empty set and infinite, nonregular sets. Write

```
P(X,Y) = {epsilon} union 0X union 1Y,
bottom = empty set,   Omega = {0,1}*,   X <= Y iff X subseteq Y.
```

Expressions and lists of premises are finite. Entailment quantifies universally
over every D-valued assignment satisfying the premises. No syntactic infinite
constant, recursive expression or top leaf is added to the input language.

**Theorem (ordinary proof below).** From an explicitly given nonempty binary
NFA A with every state accepting, including optional epsilon transitions, one
can construct in deterministic logarithmic space an always-satisfiable finite
bottom/product constraint set C_A and a variable query such that

```
L(A) = {0,1}*  iff  C_A entails x_start <= b over arbitrary trees
                 iff  C_A entails x_start <= b over regular trees.
```

The output uses n+2 variables and m+1 inequalities for n states and m edges.
Every expression has product depth at most two. Consequently exact arbitrary-
and regular-tree bottom/product entailment are PSPACE-hard, using the
CLOSED-UNIV hardness stated in HR98, Section 4. This is a lower bound, not
PSPACE membership or a claim of PSPACE completeness.

**Finite-domain exclusion.** Every produced input has no finite valuation for b.
Its finite-tree query is therefore vacuously true. This construction supplies
no finite-tree lower bound. C083's separate finite-domain NL lower bound is
not replaced or weakened.

## 2. Original construction, sources and literal obstruction

### Exact source locators

HR98 is Fritz Henglein and Jakob Rehof, *Constraint Automata and the Complexity
of Recursive Subtype Entailment*, ICALP 1998, LNCS 1443, pp. 616-627,
DOI `10.1007/BFb0055089`.

- Section 2: labelled-tree valuations and structural/nonstructural orders.
- Section 4, opening paragraphs: CLOSED-UNIV for all-accepting NFAs, its
  PSPACE-completeness, and the logspace reduction plan.
- Section 4, displayed C_k and C_A immediately before Theorem 1: transition
  inequalities and the recursive reference. Theorem 1 (published p. 622):
  nonstructural recursive subtype entailment is PSPACE-hard.
- Section 4, proof of Theorem 1: missing-word countermodel and universality
  direction; inspect the largest solution's top labels in the negative case.
- Section 4.1, Theorem 2 (published p. 623): finite-tree variant with the
  one-sided reference premise `beta times beta <= beta`.

[Institutional publication record](https://researchprofiles.ku.dk/da/publications/constraint-automata-and-the-complexity-of-recursive-subtype-entai/).
[Author-uploaded full text](https://www.researchgate.net/publication/2310458_Constraint_automata_and_the_complexity_of_recursive_subtype_entailment).
[Author PDF URL](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf).

**Source-access boundary.** I read the author's full-text HTML, including the
transition formulas and both directions of Theorem 1, rather than only its
abstract. The author PDF and ResearchGate PDF requests failed. No PDF bytes,
checksum or page-image verification is claimed. The page numbers above are
corroborated by the pinned repository's prior
[primary-source readback](../notes/prior-work/finite-tree-comparison-2026-09-20.md);
section/theorem/formula locators were checked anew in the full text. The
HTML mathematics has imperfect font extraction. Visual PDF verification remains
an independent review item, not an assumed PASS.

### Reconstructed original constraints

Rename HR's letters f,s to 0,1. Associate alpha_i to each state and a fresh
delta_k to each labelled transition. A transition contributes

```
i --0--> j : alpha_i <= alpha_j times delta_k
i --1--> j : alpha_i <= delta_k times alpha_j
i --epsilon--> j : alpha_i <= alpha_j.
```

Add `beta = beta_1 times beta_2`, `beta = beta_1`, `beta = beta_2`, where each
equality is two inequalities. Query `alpha_start <= beta`. The reference is
therefore the full product tree Omega. The input uses no top literal, but the
original labelled-tree domain includes an explicit top leaf strictly above
Omega. Product arguments are covariant; top is not below a product.

Here is an independent ordinary reconstruction of the two implications,
without treating the paper's largest-solution argument as an unexplained oracle.
For a state i let L_i be its path language. All states accept, so L_i contains
epsilon and is prefix-closed. Construct a source tree T_i with a product at
every word in L_i and a top leaf at every first missing word. Assign every
delta_k=top and beta=Omega. If i --a--> j, then a L_j is contained in L_i;
this proves the appropriate product upper bound. Epsilon edges use
L_j subseteq L_i. Inclusion of such path languages reverses the order of these
product/top trees: more product positions replace top leaves by smaller trees.
Thus this is one simultaneous valuation of every original variable. If v is
missing from L_start, its first missing prefix has a top leaf, while Omega
has a product there. The query fails.

Conversely, for universal A, every word w has a run extending through w0.
Following that run's upper bounds forces a product or bottom at w in any
satisfying state tree; it rules out a top or incompatible constructor there.
A bottom encountered earlier makes the comparison with Omega succeed below
that point. Applying this to every finite w yields alpha_start <= Omega for
every original valuation, not merely for the displayed countermodel family.
This also explains why additional arrow-valued variables in HR's larger
ambient signature cannot invalidate the universal direction.

### Where top matters

Top is available for the unconstrained delta_k variables and for missing-path
leaves. Those leaves distinguish the state tree from the all-product reference.
The universal quantifier ranges over these assignments even though no input
term spells top. Removing these valuations changes the problem.

For the finite variant, a separate reconstruction uses lower finite truncations
of the directed state constraints and a finite complete product reference B_h
with top leaves at depth h. It satisfies `B_h times B_h <= B_h`; choosing h past
a preserved top-labelled separator keeps the query false. This is not a
uniform truncation claim for the whole system: the reference premise is not a
directed state constraint. The Section 4.1 HTML displays a bottom cut in its
truncation definition; its glyph was not checked against a PDF image. The
present arbitrary-tree proof does not depend on that finite argument.

### Minimal obstruction to the literal transfer

In D, `P(B,B) <= B` forces epsilon into B and closes it under both binary
prefixes. Induction on word length gives B=Omega. Hence both the original
reference equalities and its one-sided variant make `X <= B` true for every X.
For the one-state NFA with no labelled transitions, L(A)={epsilon}, but the
literal target query is true. In the original domain, alpha_start=top and
beta=Omega is a countermodel. In arbitrary/regular target semantics the
collapse is not vacuity: assigning Omega to all variables satisfies the
original constant-free premises.

More generally, no order-reflecting map from the original product/top domain
to D can both preserve the binary product operation P and be monotone.
Indeed E(Omega)=P(E(Omega),E(Omega)) forces E(Omega)=Omega, and
Omega <= top forces E(top)=Omega too. It cannot reflect top not<=Omega.
This excludes precisely that class of maps, not other reductions. The repair
below changes the product representation, escaping its hypothesis.

## 3. The marker context and finite output

Define a context using only the permitted constructors:

```
H(X,Y) = P(P(X,Y), bottom)
       = {epsilon,0} union 00X union 01Y.
c(0)=00, c(1)=01, with c extended by concatenation.
K = c({0,1}*) {epsilon,0}.
```

K consists exactly of the words whose positions 0,2,4,..., when present,
contain 0. It is prefix-closed and regular. We have K=H(K,K).
Unlike Omega, K omits address 1; H(Omega,Omega) also omits address 1.

**Reference lemma.** If H(B,B) subseteq B, then K subseteq B.

*Proof.* The premise inserts epsilon and 0 and closes B under prefixing 00
and 01. Starting from either inserted address and inducting on the number
of code blocks generates precisely K. Conversely H(K,K)=K, so K itself is
a permitted reference. In particular every such B is infinite. QED.

**First-illegal-address lemma.** If u is outside K, then u has a prefix c(w)1
for some binary word w.

*Proof.* Scan u in two-letter blocks. Its first violation of K is a 1 in the
first position of a block. All preceding complete blocks are 00 or 01. QED.

Given A, introduce x_i for its states and two fresh variables z,b. Output:

```
i --0--> j : x_i <= H(x_j,z)
i --1--> j : x_i <= H(z,x_j)
i --epsilon--> j : x_i <= x_j
reference : H(b,b) <= b
query     : x_start <= b.
```

H is expanded textually into two products and bottom; it is not a new symbol.
The shared z is completely unconstrained. It is NOT a syntactic top or a
caller-supplied greatest value. Its value in the positive proof is arbitrary;
the negative proof will choose Omega. Keeping separate delta variables instead
would also work, but is unnecessary.

K, Omega, L_i and powersets occur only in the proof/model construction, not in
the emitted constraint syntax. No exponential computation is hidden in the
reduction itself.

## 4. Universality implies entailment for every target valuation

Fix any satisfying assignment rho into D. Let X_i=rho(x_i) and B=rho(b).
No regularity, finiteness, encoded-image or shared-shape assumption is made.
The reference lemma gives K subseteq B.

**Run implication.** For each particular NFA run i --w--> j, and every tail v,

```
c(w)v in X_i  implies  v in X_j.
```

For an epsilon edge this follows from X_i subseteq X_j. For a 0 edge,
`00v in X_i subseteq H(X_j,rho(z))` entails v in X_j by the displayed
address formula for H. A 1 edge uses the 01 component. Induct on the finite
edge sequence, retaining epsilon moves at either end and between letters.
This proves the implication for every selected run, including empty runs.

Suppose A is universal but X_start is not contained in K. Choose u in the
difference. Prefix closure and the first-illegal-address lemma yield
c(w)1 in X_start. Universality provides a run on w0. Split it just before
its last letter-consuming edge, retaining the preceding epsilon edges.
The run implication gives 1 in X_j at the state just before that 0 edge.
But the outgoing edge bounds X_j above by some H(Y,Z), which contains no
address 1. This is a contradiction. Thus

```
X_start subseteq K subseteq B.
```

Since rho was arbitrary, the query is entailed over all arbitrary trees.
In particular, target valuations outside the intended encoded image cannot
supply countermodels. This direction, not image-only preservation, is the
critical quantifier obligation. It also immediately covers regular valuations.

## 5. Every missing word gives one simultaneous regular countervaluation

Assume v is missing from L(A). For each state i define

```
X_i = K union union_{u notin L_i} c(u){0,1}*.
b = K;  z = Omega.
```

Every X_i is prefix-closed: the stem c(u) lies in K, all its prefixes lie in
K, and the cone c(u){0,1}* supplies the rest. As epsilon belongs to L_i, no
cone has an empty stem. All the variables are assigned together by this formula.

Consider a 0 edge i->j. Since 0 L_j subseteq L_i, if u notin L_i and u=0t,
then t notin L_j. Its entire cone c(u){0,1}* is consequently contained in
00 X_j. If instead u begins with 1, its cone lies in 01 Omega. Also
K=H(K,K) subseteq H(X_j,Omega). These statements cover every address of X_i,
so X_i subseteq H(X_j,Omega). The proof for a 1 edge interchanges the two
components. For an epsilon edge, L_j subseteq L_i gives
complement(L_i) subseteq complement(L_j), hence X_i subseteq X_j.
The reference premise holds as equality at K. Thus EVERY premise holds.

The finite address c(v)1 belongs to X_start through the cone indexed by v,
but does not belong to K. The ORIGINAL query is therefore false, at that
same displayed target address. There is no change in query polarity.

**Regular realization.** Determinize A with epsilon closure. For a closed state
subset S, let R(S)=Omega if S is empty; otherwise create the regular equation

```
R(S) = H(R(step(S,0)), R(step(S,1))).
```

Use two product nodes per nonempty subset, one shared bottom node, and one
self-looping product node for Omega. Root x_i at the epsilon closure of {i}.
Add the two product nodes for K, sharing bottom. Walking a code word follows
the corresponding subset run; reaching the empty subset admits every suffix.
Otherwise only the K scaffold is present. Hence its unfolding is exactly the
formula for X_i above. This proves regularity directly, with at most
`2^(n+1)+2` nodes for the full shared model (unused subsets may be omitted).
The exponential certificate size is not the size of the reduction.

The regular countervaluation is also an arbitrary countervaluation. Combined
with Section 4 this proves both equivalences in the theorem.

## 6. Input cost, satisfiability and precise limits

With indexed states, scan each input edge and emit its one constant-size
inequality. Then emit the reference inequality and variable query. This
requires logarithmic workspace for state IDs and scan positions. There are
n+2 variables, m+1 premises, and O((n+m) log(n+2)) output bits with an explicit
variable declaration. No determinization, reachability, missing-word search,
regular-tree expansion or C081 call occurs during this translation.

Every C_A is satisfiable independently of L(A): assign every x_i=bottom,
z=bottom, b=K. The state upper bounds are automatic and the reference is an
equality. Thus the hardness does not exploit inconsistent premises.

Every finite-valued interpretation is nevertheless impossible: the reference
lemma forces the infinite K into b. In finite semantics every produced query
is true. No finite-domain transfer, tight upper bound, superpolynomial runtime
lower bound, novelty/priority claim or general explicit-top elimination theorem
is asserted. The marker construction exploits the permitted bottom literal;
it is not a hardness proof for the repository's input fragment without bottom.

## 7. Experiments and checks

[Checker](../experiments/check_hr_topfree_transfer_70.py).
[Deterministic receipt](../results/hr-topfree-transfer-70.json).
The checker imports no Subtail implementation and runs on the standard library.

Before writing the larger checker, a separate literal graph pilot checked the
no-edge, only-0-loop and two-loop one-state NFAs. Their canonical separators
are respectively 001, 011, and none. It also checked the Omega collapse and
H(Omega,Omega) not equal to Omega.

Reproduce from a checkout containing the three contribution files:

```sh
python3 experiments/check_hr_topfree_transfer_70.py --output results/hr-topfree-transfer-70.json
```

| Check | Outcome | Exact coverage / limitation |
|---|---|---|
| Marker pilot | PASS | Three one-state fixtures, separately executed before larger code |
| Exhaustive NFAs | PASS | All 4,104 one/two-state binary epsilon-NFA edge tables, fixed start 0, all states accepting |
| Independent NFA oracle | PASS | Configuration-path search on all words through 2^n-1 agrees with subset universality on those small NFAs |
| Additional NFAs | PASS | 400 seeded cases with 3-6 states; seed 2026092070 |
| Whole regular models | PASS | 33,447 canonical premise comparisons; 2,809 universal and 1,695 nonuniversal inputs; every negative has an independently checked coded separator |
| Baseline satisfiability | PASS | Bottom state valuation / K reference checked for every one of the 4,504 inputs |
| Out-of-image valuations | PASS | All 4,913 three-free-node graph encodings plus bottom for the universal one-state fixture; 106 satisfy the premises and all satisfy the query |
| Literal finite state values | PASS | All 677 prefix-closed finite values with product addresses shorter than 4; 11 satisfy both universal-loop bounds with z=Omega and b=K |
| Identity transfer | FAIL | One-state no-edge NFA; target reference becomes greatest |
| Reversed-query repair | FAIL | Universal one-state NFA, x=bottom, b=K |
| Finite-reference repair | FAIL | A finite reference cannot satisfy the lower premise; dropping it also admits a false universal-instance query |
| Independent mathematical review | UNKNOWN | Requested, no acceptance received in this session |
| Lean / full repository / native C081 | NOT RUN | No full checkout or Lean execution claimed |
| Original PDF page images | NOT RUN | Primary full-text HTML read; PDF retrieval failed |

Execution environment is Python 3.13.5, Linux x86_64. No search cap pruned any
listed finite experiment. These counts do not prove an all-input entailment
answer; Sections 3-6 supply the ordinary proof. The finite-state-value test
still assigns an infinite reference: it is NOT a finite-domain entailment test.
The generated graph family contains duplicate tree meanings; counts are graph
encodings, not pairwise distinct valuations.

## 8. Coordination, provenance and integrator handoff

Read at the pinned base: AGENTS.md, research/problem.md, current STATE and
research tracker, C080-C085 ledger entries, relevant A010/A017 histories,
the extension/finite-literature records, #70 and recent #37 ownership comments.
C083 remains the existing reviewed NL bound in shared records. The current
publication integrator retains the manuscript and shared ledgers.

Ownership claim: #70 comment 5750331150. Cross-post and review request:
#37 comment 5750356146. Pre-implementation ordinary proof outline and review
request: #70 comment 5750360587. The coordinator explicitly agreed this
disjoint scope in #70 comment 5750364870, while stating that review had not
yet been performed or assigned. Scope agreement is not mathematical review.
Main was observed at e2c981b44418ca12a689e8ef3c4b63f62d750e64 before worker
publication; this additive branch remains based on the pinned 19b06d4 source.
No combined-tree validation against that newer main is claimed.

GitHub connector reads/writes worked. A container git clone failed DNS.
Local work therefore uses a clearly labelled contribution-only git repository
and its separate worktree; it is not represented as a complete source checkout.
No unrelated worktree, stash or unpushed work was inspected or changed.
Only this note, its independent checker and its receipt are proposed for the
worker branch. No main push, issue closure, manuscript edit, shared ledger
mutation, Lean/module/toolchain change, or new global C/E allocation is made.

### Proposed integrator text (not applied)

A new ordinary theorem, pending independent review, reduces binary CLOSED-UNIV
to arbitrary bottom/product entailment with n+2 variables and m+1 depth-two
premises. The context H(X,Y)=((X times Y) times bottom) creates a proper regular
reference. An all-valuations path argument proves the universal case; an
explicit regular countervaluation proves the missing-word case. The claimed
consequence is PSPACE-hardness for arbitrary and regular trees, not finite
trees or PSPACE membership. Retain C083's independently established finite NL
claim. Allocate/update a canonical claim only after reviewing this contribution.

### Remaining gates

An independent reader should recheck the run implication, earliest marker,
epsilon transitions, simultaneous countermodel and logspace size bound. Also
visually verify the original PDF's source locators and finite-truncation glyph.
These review/access gates are explicit; no missing implication in the new
ordinary reduction is being hidden behind the experiments. Wider priority and
matching-upper-bound investigations are outside this contribution.

No Lean formalization was started before that review. If formalization is
selected later, the critical declarations are H's address formula, the lower
reference lemma, the run implication and the explicit missing-word model.
The finite experiment checker and source-reader account should remain separate
from a future checked theorem and from existing C081 runtime certificates.

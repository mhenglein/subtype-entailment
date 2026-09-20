# Explicit-top entailment by two projections

Date: 2026-09-20. Actor: `explicit-top-dual-projection-20260920`.
Workstreams: A010/A011/A018; issue #71; coordination #37.
Input revision: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Branch: `codex/issue71-dual-projection-20260920`.
The exploratory end-to-end outline was committed **before implementation** at
`cb8542be1bc3947e2c2ad9e66c88c9408dded807`; this note expands that route.

**Status:** complete ordinary reduction argument for the full stated signature,
using C081. Independent mathematical review is **PENDING**, not claimed performed.
The separate new Lean module targets the critical arbitrary-language lifting
and entailment decomposition; its execution status is recorded below. Neither
this note nor the experiments promote a shared claim or close issue #71.

## 1. Exact theorem and dependency

**Theorem.** Entailment of finite conjunctions of inequalities between finite
expressions over variables, bottom, explicit top and one covariant binary
product is decidable when valuations range over **all** arity-consistent trees
on this signature, including infinite nonregular trees. There is an effective
reduction using at most four calls to the existing top-free C081 decision.
There is no satisfiability promise. Inconsistent premises entail every query.

The one imported decision result is exactly
`Subtail.EntailmentDecision.entailsCheck_correct` at the input revision:

```lean
entailsCheck (G : Input n) (s t : Expr n) = true <-> ExprEntails G s t
```

Here `Expr` has variables, bottom and binary product, and its tree values are
arbitrary prefix-closed subsets of `{0,1}*`, ordered by inclusion. The source
was read in `ExpressionNormalization.lean`, `TreeSemantics.lean` and
`EntailmentDecision.lean`, and compared with the C081 ledger entry. The theorem
has no model-regularity, SAT, U/F, C030 or supplied witness-bound hypothesis.
This attempt imports that result; it does not re-audit its entire dependency
closure or report a fresh whole-C081 build.

All other mathematical implications needed for this reduction are proved
below. No finite- or regular-tree completeness theorem is assumed. C085 and
all existing tree definitions, decision modules, imports, ledgers and paper
files are unchanged.

## 2. Labelled domain, coinductive order and totalized observations

Write `W={0,1}*`, with empty word `e`, and concatenate words on the right.
A tree is a pair `(D,label)` where `D` is a nonempty prefix-closed subset of W,
`label:D->{bottom,product,top}`, and

```text
w0 and w1 belong to D exactly when label(w)=product.
```

Equivalently, each product node has exactly its two ordered children and a
bottom or top node has no children. There is no finiteness, finite-state or
decidable-membership condition on D or label. Bottom and top are distinct
one-node trees. Product attaches its arguments below a fresh product root.

Define the order coinductively: bottom is below everything, everything is
below top, and two products compare exactly when their corresponding children
compare. There are no other root-compatible comparisons. Formally, take the
greatest fixed point of this root rule. It also equals the intersection of
all finite-depth approximants, starting with the universal relation, since
for this fixed signature the root rule commutes with decreasing intersections.
Thus infinite products are not identified with top-labelled leaves.

For each finite address w, start at the root and follow w while the label is
product. On encountering bottom or top, keep that label for the rest of the
address. This defines a *totalized label* at every word, including virtual
addresses below a leaf. Set

```text
P(t) = {w : the totalized label is product or top},
H(t) = {w : the totalized label is top},
Q(t) = W \ H(t).
```

P is prefix-closed: if the observation at an extension is not bottom, no
prefix observation is bottom. H is a right ideal: once top has been observed,
every right extension is still top. Also H is contained in P. Equivalently,
P and Q are prefix-closed and `P union Q = W`.

**Lemma 1 (exact representation).** Trees correspond bijectively to pairs
`(P,H)` with P prefix-closed, H a right ideal and `H subseteq P`; equivalently,
to prefix-closed covering pairs `(P,Q)`.

*Proof.* Given such P,H, define a total label to be bottom outside P, top in
H, and product in `P\H`. Keep precisely the addresses all of whose proper
prefixes have product labels. The empty address is kept. This domain is
prefix-closed, and an address has both children exactly when its label is
product. Prefix closure of P makes all descendants of a bottom observation
bottom. The right-ideal property of H makes all descendants of a top
observation top. Consequently totalizing this actual labelled tree recovers
exactly P,H at **every** word. Conversely, pruning a totalized original tree
at its first leaves recovers its domain and labels. This proves both inverse
identities without imposing any condition on infinite branches. QED.

**Lemma 2 (exact order).**

```text
s <= t  iff  P(s) subseteq P(t) and H(s) subseteq H(t)
        iff  P(s) subseteq P(t) and Q(t) subseteq Q(s).
```

*Proof.* On the three labels in the chain `bottom < product < top`, an
observation is below another exactly when both its non-bottom bit and its
top bit are at most the corresponding bits of the other. A root-compatible
comparison implies this pointwise condition at every address: either a leaf
already makes the comparison automatic, or both roots are products and one
continues with the chosen child. Conversely, the pointwise condition implies
the root rule, and, for two products, implies the same pointwise condition
for both residual subtrees. Induction gives every finite-depth approximant;
hence it gives the coinductive order. Taking complements yields the Q form.
QED.

The exact constructor equations are

| Value | P | Q |
|---|---|---|
| bottom | empty | W |
| top | W | empty |
| product(s,t) | `{e} union 0P(s) union 1P(t)` | `{e} union 0Q(s) union 1Q(t)` |

For H the product equation is `0H(s) union 1H(t)`, **without** the root.
Swapping bottom and top at every actual node defines an order-reversing
involution d, preserving products, with `P(d(t))=Q(t)`.

In particular the full infinite product tree Omega has `(P,H)=(W,empty)`,
whereas explicit top has `(W,W)`. Thus top is not below Omega or `top*top`.
P alone deliberately forgets that distinction; the second component restores it.

## 3. Exact naming and the two finite target systems

Name every subexpression of the premises and query by a fresh variable,
retaining one common name for each original variable. Add an exact equation
for each named bottom, top or product. A product name p for `s*t` receives
`p=name(s)*name(t)`. Replace each original comparison by the corresponding
comparison between names. The resulting finite normalized system S has forms

```text
x <= y;    x = bottom;    x = top;    x = y*z.
```

The query is `a<=b` between its two names. Equations can always be written as
two subtype inequalities, since Lemmas 1 and 2 imply antisymmetry.

**Lemma 3 (naming).** Models of the original input extend to models of S by
evaluating the finite named subexpressions. Conversely, restriction of any S
model to original variables is a model of the original input, and induction
on finite expressions identifies every name with its expression. The two
query values are unchanged in both directions. Thus satisfiability and failed
queries transfer in both directions. Repeated variables and occurrences are
not given independent valuations. The construction is effective and finite.

Construct `S+` over the C081 domain as follows. Preserve variable inequalities,
bottom equations and product equations. Replace every top equation by
`x=omega`, where omega is one new common variable, and append
`omega=omega*omega`. In the top-free domain this equation has the unique
solution W: it forces the empty address, and membership of w forces membership
of both `0w` and `1w`; induction on word length gives every word. Conversely W
satisfies it. This is use of Omega as a **projection value**, not an embedding
of the source top leaf.

Define the dual normalized system `dS` by reversing variable inequalities,
swapping bottom and top equations and preserving product equations. Set
`S-=(dS)+`, using its own fresh omega. Dually applying d returns S.

A model A of S+ is exactly a family of prefix-closed languages satisfying

```text
x<=y:    A_x subseteq A_y;
x=bottom: A_x=empty;
x=top:    A_x=W;
x=y*z:    A_x={e} union 0A_y union 1A_z.
```

A model B of S- satisfies the reversed inclusions, swaps the constant
languages, and has the same product-language equations. Lemmas 1 and 2 show
that every labelled S model gives both an A model and a B model. The difficult
converse is not obtained by pairing arbitrary independently chosen A and B:
for the empty system they could both omit the empty word, violating coverage.
The following construction supplies the missing compatibility.

## 4. Least forced-top languages: the lifting lemma

Let H be the family of all facts admitting a **finite derivation** from the
following rules, interpreted for every finite word w:

```text
x=top:          H_x(w)                         [all-word seed]
x<=y:          H_x(w) -> H_y(w)
x=y*z:         H_y(w) <-> H_x(0w)
               H_z(w) <-> H_x(1w).
```

Each displayed equivalence comprises two inference rules. There is no root
seed for a product equation, and no bottom seed. This defines H for arbitrary
systems by finite inductive derivations; cycles do not require truncation.
For finite S it is a finite rule scheme with regular all-word seeds. We do
not have to compute H to execute the four-call reduction.

**Lemma 4 (three invariants).**

(a) Every H_x is a right ideal.

(b) For every positive model A, `H_x subseteq A_x` for every variable x.

(c) For every negative model B, `H_x intersection B_x = empty` for every x.

*Proof of (a).* Given a derivation of `H_x(w)` and any common suffix v,
append v to the word in **every** fact in the derivation. An all-word seed
remains a seed. The variable-inequality rule preserves the word. Each push
or pop rule remains valid because `(iw)v=i(wv)`. Induction on the finite
derivation therefore derives `H_x(wv)`. This is right-suffix closure, not
prefix closure of H and not a bounded-cycle argument.

*Proof of (b).* All-word seeds are contained in `A_x=W` at top constants.
The positive inclusion for x<=y preserves the property. The positive product
equation supplies both push and pop implications at nonempty addresses.
Induction on the derivation gives the result for every word and variable.

*Proof of (c).* Equivalently show that `W\B_x` contains every derivable fact.
At a top constant the negative model has `B_x=empty`. For x<=y the negative
inclusion is `B_y subseteq B_x`, hence its complement propagates from x to y.
The negative product equation gives `B_x(iw) iff B_child(w)`; its negation
therefore supplies both push and pop implications for the complements.
Induction on the derivation proves disjointness. QED.

**Lemma 5 (positive projection lifting).** Suppose S- is satisfiable. Then
**every** positive S+ model A is the P projection of a labelled model of the
whole S.

*Proof.* Choose a negative model B only for the consistency argument. Use
the family H just constructed. By Lemma 4(a,b), each `(A_x,H_x)` satisfies
Lemma 1 and therefore reconstructs a labelled tree `rho(x)` with exactly
those observations. It remains to check every normalized clause:

- For x<=y, the A model supplies `A_x subseteq A_y` and the derivation rule
  supplies `H_x subseteq H_y`. Lemma 2 gives `rho(x)<=rho(y)`.
- For x=bottom, `A_x=empty` and containment makes `H_x=empty`.
- For x=top, `A_x=W` and the all-word seeds give `H_x=W`.
- For x=y*z, the A product equation already holds. All nonempty H addresses
  satisfy exactly the two child equations by the paired rules. At the root,
  `e in B_x` by the B product equation, so Lemma 4(c) forbids `e in H_x`.
  Hence `H_x=0H_y union 1H_z`, with no root. The constructor table and
  injectivity from Lemma 1 give the **exact labelled product equality**.

These checks use one common H family for all variables and all clauses; they
do not join independent atom witnesses. They hold equally for recurrent
systems and arbitrary, potentially nonregular A. The chosen B need not be
paired with A, and need not equal the reconstructed Q projection. QED.

**Lemma 6 (negative lifting and satisfiability).** If S+ is satisfiable,
every S- model B is the Q projection of a labelled S model. Further,

```text
Sat_labelled(S) iff Sat_topfree(S+) and Sat_topfree(S-).
```

*Proof.* Apply Lemma 5 to dS, using `d(dS)=S`, and then apply the tree
involution d to the resulting entire valuation. Products and constants are
preserved/swapped exactly as required, and every inequality reverses. The
P component before d is precisely the Q component afterwards. This proves
negative lifting with all variables shared. Projection gives the forward
SAT implication. For the reverse implication, choose any A model and apply
Lemma 5 using the existence of a B model. QED.

This is stronger than preservation on already encoded source trees: it
lifts **every target valuation** once the opposite projected system is
satisfiable. Therefore extra target valuations cannot create spurious
countermodels in the final reduction.

## 5. Entailment equivalence, correctness and termination

**Lemma 7 (unconditional decomposition).** For all normalized finite S and
query names a,b,

```text
Ent_labelled(S,a,b)
iff not Sat_topfree(S+) or not Sat_topfree(S-)
    or (Ent_topfree(S+,a,b) and Ent_topfree(S-,b,a)).
```

*Proof.* If either projected system is inconsistent, Lemma 6 makes S
inconsistent and both sides are true by vacuity. Suppose both are
satisfiable. If both projected entailments hold, every labelled model has
both inclusions in Lemma 2, hence satisfies the source query. Conversely,
a positive target countermodel A failing `A_a subseteq A_b` lifts by Lemma 5
while preserving that entire A family, and so still falsifies the source
query. A negative target countermodel B failing `B_b subseteq B_a` lifts by
Lemma 6 while preserving B and again falsifies the source query. These two
cases exhaust failure of the conjunction. One countermodel is enough; there
is no requirement or claim that two separately failing projected valuations
can be glued to each other. QED.

If a failed projected inclusion is witnessed by w, the lift preserves that
failure at the **same totalized observation address w**. A literal label clash
in the actual source domains may occur earlier on the path: for example top
versus `bottom*bottom` clashes at the root although their P languages first
differ at a one-letter word. The theorem requires the same failed source
query, not a false assertion that w is necessarily an actual node of both
trees. The experiment's same-word counts refer to projected observations.

Let `E(C,s,t)` denote the total C081 Boolean. The fixed inequality
`bottom*bottom <= bottom` is false in every top-free valuation. Therefore

```text
Unsat(C) = E(C, bottom*bottom, bottom).

Answer(S,a,b) =
  Unsat(S+) or Unsat(S-)
  or (E(S+,a,b) and E(S-,b,a)).
```

This uses at most four C081 calls, after the finite naming and projection
translations. Lemma 7 proves both soundness and completeness, including
inconsistent premises. Each call is on a finite input in the exact C081
signature, so its termination theorem applies. The infinite H construction
is used only in the proof of the reduction, not as an unbounded computation
hidden in this algorithm. Lemma 3 transfers the result back to the original
finite expressions. This proves the theorem in Section 1.

No practical runtime, tight complexity class, universal witness bound,
finite-tree result, other-constructor or variance result is asserted.

## 6. Why the old proof fails, and why this one does not repeat it

The first failure in the old product-address closure is a lower premise
`y*z<=x`: it does not force an **actual product label** at x, since x may be
top. Its push rules likewise cannot assert actual children below that leaf.
Here P records non-bottom *totalized* observations instead of actual product
addresses. A top leaf correctly contributes every word to P. H separately
records its absorbing top label and is never given an unconditional product
root seed. Thus the positive propagation is sound for P, and the negative
model prevents incorrect top labels at **exact product equations**.

The following unsuccessful routes remain distinct:

1. Replacing top by Omega alone loses order reflection: `top<=top*top` is
   false, while the image is true. This is just one projection, not Lemma 7.
2. Replacing top by bottom loses preservation, already for `bottom*bottom<=top`.
3. A fresh unconstrained top variable fails universal validity of `x<=top`.
4. Arbitrary independently chosen positive and negative models may fail
   coverage; the empty system with both projections empty is a counterexample.
   Lemma 5 constructs a compatible second component instead.
5. Dropping the consistency gates can lose vacuous entailment. For example,
   `x=top, x=y*y` is inconsistent in the labelled domain. Its positive projection
   is satisfiable with x=y=Omega, while its negative projection is inconsistent.
   An unrelated query a<=b can fail in the positive projection but is vacuously
   true in the source.
6. H must start with every right extension at a top constant. Root-only seeds
   do not represent a top leaf, even with no other clauses.

These failures refute the named shortcuts, not every encoding. The opposing
undecidability route was kept open at the initial outline. Given Lemmas 1-7
and C081, an undecidability reduction with exactly these hypotheses would
contradict the composed decision; it would have to expose an error in this
proof or change the signature, valuation domain or logical fragment.

## 7. Independent-algorithm tests and their boundaries

`experiments/check_explicit_top_dual_projection.py` imports no existing Subtail
implementation. One checker follows literal labelled graph pairs, accepting
bottom-left/top-right and recursively comparing product children. Visited
pairs make it an exact test on the unfoldings of finite graphs, even cyclic
ones. A second literal finite-tree recursion cross-checks that checker.

For the lift, a separately implemented epsilon NFA computes H. Its states
are the normalized variables plus one accepting universal-suffix state f.
Top variables have epsilon edges to f; f has both letter self-loops. An
inequality x<=y adds an epsilon edge y->x, and a product equation x=y*z adds
letter edges x-0->y and x-1->z. Saturate epsilon closure and, whenever a path
x-epsilon*-i-epsilon*->q exists for a product equation, add an epsilon edge
from its i-child to q. Only finitely many epsilon pairs can be added.

For clarity, its exact-language justification is separate from the main
four-call decision. Give state f the language W and each variable the least
H language. Every initial path preserves the corresponding language inclusion;
every new epsilon edge does so by the pop rule. Induction on added edges and
paths proves that all accepted words are in H. At saturation the recognized
languages contain the seeds and are closed under every push, pop and inclusion
rule; induction on H derivations proves the opposite inclusion. Thus the
NFA accepts exactly H. Product of its deterministic subsets with the supplied
positive graph, cutting at accepted top states, constructs a finite labelled
graph whose unfolding has the prescribed P and H. An independent literal
graph checker then verifies every original premise and projected equality.
These are supporting finite-graph implementations, not the C081 decision.

The script also compares with literal finite H derivations; absence of a
derivation beyond its stack cap is UNKNOWN. Its positive facts must agree
with the NFA, and no negative completeness is inferred from the cap.

Executed locally:

```text
python3 experiments/check_explicit_top_dual_projection.py --output results/explicit-top-dual-projection.json
Python 3.13.5; seed 2026092071; Linux x86_64
```

The saved receipt records the script hash and all bounds. Results:

- 1,444 finite-tree order pairs and 5,184 cyclic-graph order pairs passed.
- 393 normalized systems were inspected: every two-variable system of at most
  two clauses, 250 seeded larger clause sets, and six boundary/recurrent systems.
- 5,156 projected valuations lifted and passed all original premises;
  292 failed projected comparisons retained their observation address.
- 2,384 source-model projection checks passed. Six additional three/four-node
  targeted lifts cover nested top cones, mutually recurrent products and
  repeated shared children, with 1,397 top-cone membership checks.
- 11,790 bounded-derivation comparisons and 33,838 right-extension checks
  passed; no NFA-positive comparison lacked a derivation within the tested cap.
- In 217 systems the finite graph corpus did not provide witnesses for both
  projections. Their corpus search result is **UNKNOWN**, not UNSAT.

The broad model enumeration uses at most two graph nodes; additional targeted
models use at most four. Finite-tree depth is two; direct derivation stack cap
is six; comparison word depth is three; tested right-extension depth is two.
The counts are finite evidence for the implementations. The general theorem
comes from the unbounded proofs above, not the corpus. The C081 executable
was not run by this local experiment.

## 8. Selective formalization and review status

The NEW module `lean/Subtail/ExplicitTopDualProjection.lean` imports only Std.
It defines arbitrary-language systems, positive models, covering paired models,
inductive `ForcedTop`, and proves the precise critical statements:

```text
forcedTop_suffix
forcedTop_in_positive
forcedTop_disjoint_negative
remaining_model
positive_projection_surjective
negative_projection_surjective
satisfiable_iff_projections
entails_iff_projections
positive_countermodel_lift
```

The last address theorem preserves the supplied **projected** address, as
explained above. The module does not silently identify its paired semantics
with existing TreeSemantics. Lemmas 1-3 and the finite C081 compiler connection
are ordinary proof obligations proved in this note, not claimed checked by
that module. No new full expression-level Lean decision is claimed.

Execution receipt: **PASS**, remotely on the pinned source below. The isolated
workflow `.github/workflows/explicit-top-dual-projection.yml` ran at commit
`6c967957e94f537bc6a74c8dac8cccc9082fdd97`; the module was introduced unchanged
at `50835ab03c0853b918adc7a8ca15b5d55a139e4b`. GitHub Actions run
[35516481506](https://github.com/mhenglein/subtail/actions/runs/35516481506),
job `106093182926`, completed successfully on 2026-09-20. Its actual logs were
read, not inferred from a queued or skipped status.

```text
Lean 4.33.1, x86_64-unknown-linux-gnu, toolchain commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
lake build Subtail.ExplicitTopDualProjection                  PASS
lake env leanchecker Subtail.ExplicitTopDualProjection       PASS
all 29 explicitly named declaration dependency closures     PASS
module SHA256: bac45e1f4613e6c95035b3d24f42950f3bf3fcd98324ee25bd8515888e130993
```

There are 14 explicit theorems and 15 other named declarations. No `sorryAx`
or custom axiom occurs. Non-theorem declarations are axiom-free; the classical
existence/entailment proofs use only the standard `propext`, `Classical.choice`
and `Quot.sound`. Core forced-top induction lemmas are axiom-free. The action
restored an existing Lake cache, then freshly built the new Std-only module;
this is not claimed to be a clean full-C081 rebuild. The local container has
no lean/lake, so its local Lean check is **NOT RUN**. The full default
repository suite is **NOT RUN** in this attempt.

No independent mathematical reviewer was available in this session. A request
was posted with the scope in #71/#37; it is **PENDING**, not fulfilled by the
author's readback, the independent algorithms, or Lean kernel checking. The
principal review target is the labelled-tree correspondence plus the universal
projection-lifting proof, especially root exclusion, suffix orientation,
shared variables, vacuity and the exact C081 invocation.

## 9. Primary-source boundaries and provenance

The relevant source histories A010/A011/A018, the extension study and its
independent readback, AGENTS, problem, STATE, claim ledger and current #71/#37
coordination were read at the input revision. In particular A010's historical
missing SAT gate and A011's untransferred converse/undecidability proposals
are not silently reused. The extension readback correctly refuted the three
naive top substitutions; it did not rule out this two-component lifting.

Primary literature inspected for the boundary, not imported as the decision:

- Niehren and Priesnitz, *Entailment of Non-Structural Subtype Constraints*
  (1999), Section 2 and Theorem 14, author PDF
  <https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf>.
  Its restricted syntax has variable inequalities and product equations,
  excluding equations to bottom or top; both labels remain in its ambient
  tree domain. Its restricted PSPACE result is not an upper bound for the
  full input handled here without a further reduction.
- Su, Aiken, Niehren, Priesnitz and Treinen, *The First-Order Theory of
  Subtyping Constraints*, Theorems 3.8 and 3.10, author manuscript
  <https://www.ps.uni-saarland.de/Publications/documents/fot_04.pdf>.
  The displayed PCP construction uses quantified first-order formulas.
  Theorem 3.10 is full first-order undecidability with a binary symbol and
  bottom, including infinite trees; it does not settle this universal
  implication of finitely many inequalities.
- Schubert, *On non-structural subtype entailment*, arXiv:2109.02458,
  <https://arxiv.org/abs/2109.02458>. The current record marks v2 withdrawn
  and identifies an error in Lemma 5.5 invalidating the subsequent construction.
  Its advertised finite/regular PSPACE result is not used.

PDF text was read through the web tool. Requested PDF screenshots returned
Internal Error; no successful visual PDF verification is claimed. The C081
source theorem, not any unverified external announcement, is the decision
dependency of this proof. No publication-priority claim is made.

Only newly reserved paths were written. The local workspace is an isolated
**partial-source** git worktree at `/mnt/data/subtail-issue71`, not a clone of
the input commit. Remote branch ancestry, not that local synthetic root,
records the source base. Other workers' checkouts, stashes and unpushed work
were not inspected. No main integration, branch retirement, shared-ledger
write, or alteration of C081/C085 semantics was performed.

## 10. Handoff and next decisive question

The general theorem is offered as an ordinary proof with a deliberately small
critical formalization, not as a completed independently reviewed release.
Issue #71 stays open pending independent mathematical review. The selective
formalization receipt is PASS at the exact source above. Any further expression-level formalization must keep the new
signature separate and prove the labelled-tree/paired-language identification
and finite naming/projection compiler correspondence, rather than assume them.

The next decisive question is: **does an independent reviewer confirm Lemmas
1-7, in particular that every target countermodel lifts under the opposite
SAT gate, over arbitrary nonregular trees?** An actual counterexample would
refute this proposed transfer only; absent such a defect, C081 discharges the
remaining decision calls with no new automaton or witness bound.

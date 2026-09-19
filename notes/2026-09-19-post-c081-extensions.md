# C081: extensions, transfers and small obstructions

Date: 2026-09-19. Actor: `post-c081-20260919`.
Base: `c946d86b9e65da2877e0df42c710abbdcb5a4037`.
Workstreams: A010/A017/A018, programme [#53](https://github.com/mhenglein/subtail/issues/53).
Status: **reviewed ordinary regular-transfer proof and feasibility study**.
No extension theorem below is presented as a new Lean theorem.

## Route outline and exact targets

The starting theorem C081 decides all finite expression entailment inputs over
bottom and one covariant binary product. Values are arbitrary possibly infinite
trees, represented by prefix-closed sets of product addresses. This study asks:

1. Does the same input have the same entailment answer over regular trees?
2. Does that equivalence extend to finite trees?
3. Can a new nullary top constructor be represented by the existing greatest
   tree without changing entailment?
4. Which steps would need new arguments for different arities, multiple
   constructors or contravariance?

The first route is forward from the canonical model and minimum-stack
factorization. A finite separating word gives finitely many seeds; their
reachable configurations have regular stack languages; prefix closure turns
those languages into finitely represented trees. Every implication is proved
below. The finite-tree and naive-top routes are tested by literal counterexamples.
For other signatures the outline identifies open obligations, not conclusions
obtained by silently replacing the alphabet in the Lean files.

The weakest useful regular transfer is existence of one regular countermodel
when any countermodel exists. Preserving every arbitrary valuation is unnecessary.
Conversely, a counterexample to one proposed top encoding does not decide the
top extension or exclude a different encoding. The opposing undecidability
route would need a computation encoding that uses the extra label; the
obstructions here do not supply one.

## 1. Effective regular countermodels

Fix a normalized finite system C on n controls and a failed query a <= b.
The canonical separation theorem supplies a finite word w. Its finite seed
set S contains the forced roots and (a,u) for all prefixes u of w. Let W be
the finite push/pop/epsilon system of the canonical propagation rules, with
the stack's first letter on the left. Write W^op for its reverse.

We use two checked source statements, with their exact mapping:

- `CanonicalModel.not_entails_iff_canonical` supplies the closure of precisely
  S as a model of C containing (a,w) and omitting (b,w).
- `StackReachability.reaches_iff_normal` says that (p,u) reaches (q,v) exactly
  when u=az, v=cz and some control m satisfies Pop_W(p,a,m) and
  Pop_(W^op)(q,c,m). Its system is the same W; there is no bound on c or v.

For controls q,m, define the word language

```text
L(q,m) = {c : Pop_(W^op)(q,c,m)}.
```

**Lemma R1 (effective Pop language).** The language L(q,m) is accepted by an
effectively constructible finite epsilon-NFA.

*Proof.* Its states are the n
controls, alphabet {0,1}, initial state q and only accepting state m. It has
an epsilon edge x -> y for every balanced pair E_(W^op)(x,y), and an a-labelled
edge x -> y for every pop-a rule x -> y of W^op. A run accepts exactly when
it consumes the whole word and reaches m, allowing epsilon moves at both ends.
Missing labelled edges reject that run. The balanced relation is a computable
finite table, so this construction is effective. For the empty word, an NFA
path consists only of balanced edges. Reflexivity and transitivity of Balanced
make their composite exactly a balanced pair, including a path of length zero.
This is Pop on the empty word. Conversely each balanced pair is itself an
epsilon edge.

For a word av, split an accepting path at its first letter-consuming edge.
Its preceding epsilon path is a balanced pair; that edge is a pop-a rule;
the rest accepts v. By induction this is precisely the recursive Pop clause.
Conversely a nonempty Pop derivation supplies those three parts, and the
induction hypothesis supplies the remaining NFA path. This proves both
inclusions by word-length induction. In particular epsilon closure is allowed
at both ends, not just before the first letter. QED.

**Lemma R2 (regular reachability from finite seeds).** For a fixed seed (p,u),
minimum-stack factorization gives the exact equality

```text
{v : (p,u) reaches (q,v)}
  = union over 0 <= i <= |u| and m with Pop_W(p,u[:i],m)
      L(q,m) · {u[i:]}.
```

*Proof.* Both inclusions use the displayed factorization, taking a=u[:i]
(`take i`) and z=u[i:] (`drop i`).
The union has finitely many terms, each effectively selected by a Pop test.
Appending the fixed suffix u[i:] to an NFA is effective: attach a fresh path
with those letters at its accepting state and make only the path's endpoint
accepting. The empty suffix retains the accepting state. Taking the finite
union over all seeds gives an effective NFA for the canonical product-node
language D_q of each variable q. A finite-list seed enumeration consists of
every forced control paired with the empty word and the pairs (a,w[:i]) for
0 <= i <= |w|. This list denotes precisely the specification `pathSeeds`;
duplicate empty seeds do not change the union. No search through all words
is involved. QED.

**Lemma R3 (a prefix-closed regular language is a regular tree).** Let D be
a prefix-closed language recognized by a finite epsilon-NFA. One can construct
a finite bottom/product graph whose unfolding has product addresses exactly D.

*Proof.* Take the finite powerset DFA. Its initial subset is the epsilon
closure of the NFA initial set; its a-successor is the epsilon closure of all
targets of a-labelled edges from the current subset. A subset is accepting
iff it meets the NFA accepting set. Epsilon closure is computed by reachability
in a finite graph. Induction on the input word shows that the subset reached
after u consists exactly of NFA states reachable after consuming u and any
final epsilon moves. This proves language equality, including the empty word.

Define a finite tree graph to be a finite set of nodes, each labelled either
bottom with no children or product with two designated child nodes, together
with a root. Its unfolding has a product address u exactly when the child walk
along u exists and ends at a product node. Include one bottom node and one
node for each reachable accepting DFA state. The latter is labelled product;
its a-child is its DFA successor if that successor is accepting, and bottom
otherwise. The root is the initial DFA state if accepting, and bottom otherwise.

If u belongs to D, prefix closure puts every prefix of u in D. Hence every
state along its DFA run is accepting. Induction on |u| gives a corresponding
child walk in the tree graph ending at a product node. Conversely any child
walk to a product node follows the same DFA transitions, again by induction
on |u|, and its final DFA state accepts u. The two address languages are equal.
The construction is well-defined at rejected prefixes: prefix closure says
that none of their extensions can be accepted. There are only finitely many
graph nodes, so the unfolding has only finitely many distinct subtrees and
is regular. QED.

Apply R3 to each D_q. The required prefix closure is supplied by
`CanonicalModel.derived_closed`, since the seed list is prefix-closed and
contains all forced roots. Its denial safety and model property are those of
the canonical separating model, not additional properties inferred from the
regular-language construction.

**Lemma R4 (regularity and fresh naming).** Exact expression naming preserves
regularity in both model-transfer directions.

*Proof.* For a finite collection of regular values, take disjoint finite graph
representations. Bottom is a single bottom node. The product of any two values
is represented by the disjoint union of their finite graphs with one new
product root pointing to their two old roots. Structural induction on each
finite expression therefore yields a finite graph for its interpretation.
`Naming.extend` gives each fresh slot such an interpretation, so every slot
is regular; repeated slots may share a graph or use copies. `Naming.restrict`
only selects the original variable roots from a finite collection of regular
values, so it preserves regularity as well. The existing normalization theorem
proves satisfaction and query preservation for these same extension/restriction
maps. Together these facts prove the regular model-transfer claim. QED.

This construction gives a regular valuation satisfying C and separating a
from b at the original finite word w. The reverse direction needs no
construction: a regular countermodel is an arbitrary countermodel. Therefore
**the same normalized input entails its query over all arbitrary trees iff
it entails it over all regular trees**. Exact fresh naming extends this to
C081 expression inputs. Restricting a regular normalized valuation preserves
regularity; extending regular values by finitely many products and bottom
also preserves regularity. This checks both directions of the naming transfer.

This result is compatible with the memo's existing regular-countermodel
characterization. The contribution here is an explicit NFA construction and
its connection to the checked canonical model, not a novelty claim. Neither
NFA extraction nor the regular-tree equivalence is formalized in a new Lean
module in this study.

**Use for an interface.** Once a separating word is known, the finite graphs
above can be emitted as countermodels. Their validation need not trust the
search that found the word. Interpret the finite graphs coinductively, check
every normalized inequality by pair reachability, and check the separating
address by following finitely many child edges. Computing a witness efficiently
and building this interface remain separate engineering tasks.

## 2. Finite trees have different answers

Take the single premise x × bottom <= x and the query x <= bottom.
In product-address notation the premise forces the root of x and sends every
address u of x to 0u in x. Hence 0^j is a product address for every j >= 0.
There is no finite-tree model. The query is therefore valid over finite-tree
valuations, by vacuity.

Over arbitrary trees, let x be the regular zero spine: a product node whose
left child is itself and whose right child is bottom. Then x × bottom = x,
but x is not below bottom. This is an explicit regular countermodel. It also
shows why restricting an arbitrary model to a finite depth is not generally
a model-preserving operation. No finite-model completeness claim follows
from C081 or the preceding regular transfer.

## 3. Exact explicit-top problem

The proposed signature adds a **nullary top label**, distinct from bottom
and product. A well-formed tree has two children exactly at its product nodes;
bottom and top have none. The order is the greatest relation satisfying:

```text
bottom <= t                  for every t
t <= top                     for every t
(s0 × s1) <= (t0 × t1)        iff s0 <= t0 and s1 <= t1.
```

There are no other root-label comparisons. In particular top is not below a
product, even when both of that product's children are top. The input remains
a finite list of finite expressions and a universal query, with valuations
over arbitrary trees of this enlarged signature. This is not C081's domain:
its greatest value is the full infinite product tree Omega, with
Omega = Omega × Omega, and no separate top label.

### Even constant-free inputs can distinguish the ambient domains

Consider the finite input

```text
premises: x = x × x, x <= y
query:    y <= x.
```

Equality is shorthand for two inequalities in C081. In the top-free domain,
x × x <= x forces every binary address into x: it forces the empty address,
and membership of u implies membership of both 0u and 1u. Induction on word
length gives x=Omega, the full product tree. Since x <= y and Omega is the
greatest top-free value, y=Omega too. The query is therefore entailed.

In the explicit-top domain, choose x=Omega and y=top. The equation holds
because Omega=Omega × Omega, and Omega <= top. But top is not below Omega:
at the root it is a top leaf rather than a product. Thus the query fails.
Both assignments used in this comparison are regular. The input itself uses
neither top nor bottom, and has the product-equality/variable-inequality form
of the NP99 restriction.

This refutes the identity translation between the two arbitrary/regular-tree
entailment problems even on that constant-free syntax. It strengthens the
warning that omitting top in the formula does not remove top from valuations.
It does not exclude a different semantic reduction, nor transfer a lower bound
in either direction. Over finite trees the recursive equation has no model
in either domain, so both finite-tree entailments are vacuously true.

### A guarded reduction for inputs without bottom constants

The identity obstruction does not rule out a reduction. In fact a small
guard gives an exact polynomial reduction for the **input fragment without
bottom constants**. The source valuations still contain bottom; the restriction
is on every premise and the query, not on the values of variables.

Name each occurring source variable and each product subexpression. Add the
product equation `p = l × r` for a product name and translate inequalities and
the query to inequalities between their names. Add a fresh variable `omega`,
the equation `omega = omega × omega`, and the guard `z <= omega` for every
occurring name `z`. Only product equations and variable inequalities occur.
Thus the result has exactly the restricted syntax in Niehren–Priesnitz 1999,
Section 2, over the ambient signature with bottom, top and binary product.

**Lemma T1 (guard).** In the full arbitrary-tree domain, the equation
`omega = omega × omega` has the unique solution Omega, and `z <= Omega`
holds exactly for trees with no top label.

*Proof.* Both directions of the equation exclude a bottom or top root; the
root is product and its two children equal omega. Induction along every finite
binary word gives a product at every address, so omega=Omega. Equivalently,
the upward inequality rules out a bottom root, the downward inequality rules
out a top root, and comparison of product children propagates both directions.
For the guard, Omega has a product at every address. If z has a top label at
an address, subtype comparison with Omega fails there. If z has only bottom
and product labels, all its product addresses are included in Omega and the
comparison holds. This includes z=bottom and arbitrary nonregular z. QED.

**Lemma T2 (exact reduction).** The source entails its query over top-free
arbitrary trees iff the guarded target entails its named query in the full
arbitrary-tree domain.

*Proof.* A source model extends by evaluating each named finite expression
and assigning Omega to omega. Products of top-free trees are top-free, so all
equations and guards hold. The named query has its source value. Conversely,
T1 makes every guarded name top-free in a target model. Structural induction
on the finite syntax identifies every product name with its source expression.
Restriction to original variables is therefore a source model, again with the
same query value. These extension/restriction maps transfer countermodels in
both directions and hence transfer entailment. For regular valuations, the
same maps preserve regularity: Omega has a one-node graph, and finite products
of finite graphs are finite graphs. QED.

There is at most one name per syntax occurrence, one equation per product and
one guard per name. First rename the actually occurring variables densely;
unused names in a `Fin n` carrier do not require enumeration. The output and
the renaming computation are polynomial in the concrete input length, including
binary variable indices. This matters when n is encoded compactly.

The [NP99 primary paper](https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf),
Theorem 14, supplies a PSPACE algorithm for its restricted arbitrary-tree
problem. Applying T2 gives a **PSPACE upper bound for the bottom-free input
fragment of C081**. The separate R1–R4 regular-countermodel proof gives the same
answer, and hence the same upper bound, when source valuations are restricted
to regular trees. This latter statement uses R1–R4, not an unstated regular-only
version of NP99's theorem. The actual C081 implementation need not run in
PSPACE; this is an alternative algorithm for a restricted input class.

This reduction does not cover source bottom constants or normalized denial
constraints. It also fails for finite-tree semantics because its omega
equation has no finite solution. It is an upper-bound direction and transfers
no hardness result. Full-C081 reduction to an earlier decidable class and
exact lower bounds remain open comparison obligations. The ordinary proof
was independently read back in the [extension review](2026-09-19-post-c081-extension-readback.md);
it is not a new Lean formalization or an implemented solver.

### Three simple encodings fail

**Replace top by Omega.** Extend the translation homomorphically through
products. In the source, top <= top × top is false. In the target, its image
Omega <= Omega × Omega is true. The counterexample needs no premises or
variables. The translation does not reflect the order and therefore cannot
be used as an entailment reduction by simple substitution.

**Replace top by bottom.** The valid source inequality
(bottom × bottom) <= top becomes the false target inequality
(bottom × bottom) <= bottom. Even order preservation fails.

**Replace top by an unconstrained variable t.** The source validity x <= top
would require x <= t for every target valuation. Set x=bottom × bottom and
t=bottom to refute it. Adding t=t × t instead forces the unique full product
tree and returns to the first collapse. These failures do not exclude a
more elaborate encoding with a proved preservation/reflection theorem.

### First broken dependency

The top-free canonical model assumes that y × z <= x **forces x's root to be
a product**. With explicit top, y=z=bottom and x=top satisfy that premise,
but x has no product address at the root. The first failure is therefore
`CanonicalModel.Forced` and `derived_sound`, before the word-automaton split.
For a nonempty-child instance the push rule also fails: if y is a product
and x=top, a product address of y need not create any child address of x.

This is a failure of the present one-predicate propagation model. It is not
a proof that the enlarged order lacks least models, nor that a different
closure construction cannot work. A new semantics must distinguish bottom,
product and top at the same address and account for the absorbing upper label.
Only then can one check whether a finite summary has a replacement for strong
absorption and whether the terminal first-return argument still applies.

**Feasibility conclusion.** No tested substitution solves the explicit-top
extension. The first substantial open obligation is a sound and complete
label-aware analogue of canonical separation. A useful next experiment is
to enumerate small constraint systems and compare any proposed propagation
rules with literal three-label finite graph models. Searching only word
automata produced by the old rules would miss the semantic problem.

## 4. Other signatures: separate obligations

| Change | What survives | What still needs proof |
|---|---|---|
| One covariant constructor of fixed arity r >= 1 | Product addresses use the finite alphabet {0,...,r-1}; balanced-stack and border-rank arguments have the same form | Reprove canonical propagation, the finite query compiler's alphabet-dependent coverage/enumeration and the periodic monitor over that alphabet. The Lean development is binary. |
| One nullary constructor besides bottom | Each variable has only two possible values | Exhaust the finite valuation set. This is a direct finite-domain decision, not a use of terminal machinery. |
| Several distinct product-like constructors | Finite address alphabets remain available | A set of branching addresses loses the constructor label. Distinct incomparable constructors with identical children already have equal address sets. A labelled semantic bridge is required. |
| Contravariant function domain | Finite paths and stack systems remain plausible tools | Plain address inclusion is wrong; signs change along domain edges. A new order representation and all affected bridge proofs are required. |

For arity r >= 1, the proposed adaptation has explicit local contracts.
Replace Bool letters by Fin r. The first-return strip still has one entrance:
at a node only its matching next letter moves forward; the other r-1 KMP
edges return to the old graph. There are now r+2 graph edge labels (F,S and
one K label per letter). Every query observer must use this finite alphabet.
The coverage proof must recount its finite edge cases and the enumerator must
cover them. Border rank and first milestones do not use a binary-specific
word identity. Periodic rotation equality and finite reverse monitoring also
make sense over a finite alphabet, but their enumerations and cardinalities
must be changed and proved. This is a proposed proof transfer, not a checked
generic-arity theorem or a proof by a binary encoding.

For the contravariance boundary, put B = bottom -> bottom, with bottom least,
and use the usual rule

```text
(a -> b) <= (c -> d) iff c <= a and b <= d.
```

Then (B -> bottom) <= (bottom -> bottom) is true, while their branching-address
sets are respectively {epsilon,0} and {epsilon}; inclusion is false. Reversing
the two function types reverses this disagreement. This depth-two example
pinpoints the first semantic change without suggesting an undecidability result.

## 5. Standalone automata results

The useful mathematical interfaces are broader than the subtype frontend,
but their hypotheses stay visible:

- The terminal rank-query decision works for any finite binary partial DFA
  with directed flags and Bad states **whose finals are terminal**. It does
  not require a subtype-derived summary or absorption.
- Whole-conjunction preimage compilation is a local first-return graph
  construction. Its semantic equivalence does not assume terminal finals;
  terminal rank is used later for a bounded number of promotions.
- The infinite-continuation decision assumes strong absorption. It is not
  a decision for arbitrary flagged automata with that assumption removed.
- Finite push/pop reachability and the NFA construction above apply to an
  arbitrary finite push/pop/epsilon system. Prefix closure and the tree-model
  interpretation additionally use the subtype propagation rules and seeds.

See [the declaration map](../paper/lean-map.md) for the exact existing modules.
Packaging these as independent library interfaces would require their own
API and performance work, not a change to the mathematical assumptions.

## Experiment E053 and review record

The independent checker [check_extension_boundaries.py](../experiments/check_extension_boundaries.py)
enumerates all source bottom/top/product trees of depth at most two and
compares literal source order with order on the finite target graphs produced
by top-to-Omega substitution. The source predicate recurses over finite trees;
the target uses graph-pair reachability with a visited set, so it handles the
cycle in Omega. Explicit zero-spine, top-erasure and contravariant fixtures
are checked separately. Exact counts and source hashes are saved in
[extension-boundaries.json](../results/extension-boundaries.json).

Executed command: `python3 experiments/check_extension_boundaries.py --output results/extension-boundaries.json`.
It checked all 1,444 pairs of 38 source trees. There were 45 failures of order
reflection for top-to-Omega, and no failure of preservation within this finite
corpus. The explicit top/top-product example above is among those failures.
The separate graph-order checker agreed with literal address inclusion on 676
pairs of top-free finite trees. The zero-spine graph and both contravariant
orientations passed. None of 677 finite trees through depth four satisfied
x × bottom <= x; the all-depth impossibility follows from the proof in Section 2,
not from that census.

These are bounded checks and exact literal counterexamples. They do not
establish a general reduction, a complexity class, or any generic-arity result.
The [independent readback](2026-09-19-post-c081-extension-readback.md) confirmed
the Pop orientation, suffix concatenation and boundary fixtures, and requested
separate proofs of the NFA language, graph unfolding and regular naming steps.
Lemmas R1-R4 above supply the expanded ordinary arguments; their follow-up
review status is recorded in that note. No new Lean source was added.
The next decision is whether
the regular construction is clear enough to implement as independently checked
countermodel output; explicit top requires a new semantic idea first.

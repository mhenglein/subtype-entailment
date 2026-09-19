# C081: extensions, transfers and small obstructions

Date: 2026-09-19. Actor: `post-c081-20260919`.
Base: `c946d86b9e65da2877e0df42c710abbdcb5a4037`.
Workstreams: A010/A017/A018, programme [#53](https://github.com/mhenglein/subtail/issues/53).
Status: **ordinary arguments and feasibility study; independent review pending**.
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

Here is an explicit finite epsilon-NFA for L(q,m). Its states are the n
controls, alphabet {0,1}, initial state q and only accepting state m. It has
an epsilon edge x -> y for every balanced pair E_(W^op)(x,y), and an a-labelled
edge x -> y for every pop-a rule x -> y of W^op. A run accepts exactly when
it consumes the whole word and reaches m, allowing epsilon moves at both ends.
Missing labelled edges reject that run. The balanced relation is a computable
finite table, so this construction is effective. By induction on consumed
letters, such runs are exactly Pop derivations: balanced moves surround each
pop and include the empty-word case. Thus L(q,m) is regular.

For a fixed seed (p,u), minimum-stack factorization gives the exact equality

```text
{v : (p,u) reaches (q,v)}
  = union over 0 <= i <= |u| and m with Pop_W(p,u[:i],m)
      L(q,m) · {u[i:]}.
```

Both inclusions use the displayed factorization, taking a=u[:i] and z=u[i:].
The union has finitely many terms, each effectively selected by a Pop test.
Appending the fixed suffix u[i:] to an NFA is effective: attach a fresh path
with those letters at its accepting state and make only the path's endpoint
accepting. The empty suffix retains the accepting state. Taking the finite
union over all seeds gives an effective NFA for the canonical product-node
language D_q of each variable q. No search through all words is involved.

The canonical theorem already proves that D_q is prefix-closed. Determinize
its NFA. Each reachable accepting DFA state represents a product node, with
its two outgoing transitions representing the children. Every reachable
rejecting state represents bottom. Prefix closure ensures that a rejected
prefix has no accepted extension, so replacing its whole residual by bottom
is correct. This is a finite directed graph of bottom/product nodes, whose
unfolding has product addresses exactly D_q. It is a regular tree: only
finitely many distinct subtrees occur.

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
The regular-countermodel proof needs a separate mathematical readback of its
Pop orientation, suffix concatenation, prefix closure and normalization transfer.
No new Lean source is needed before that review. The next decision is whether
the regular construction is clear enough to implement as independently checked
countermodel output; explicit top requires a new semantic idea first.

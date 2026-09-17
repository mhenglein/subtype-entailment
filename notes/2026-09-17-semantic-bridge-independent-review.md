# Independent semantic-bridge support for the rank-query candidate

Date: 2026-09-17. Reviewed base: `8ed4f45b563cda0ae3d31980fc14e6d61a35357a`.
Workstreams A010/A017/A018. No new C/E identifier or theorem-status promotion.

**Ordinary-proof audit and executable differential evidence. No substantive gap
was found in the older bridge arguments audited below. This is a separate
AI-assisted review informed by the existing arguments, not a blind derivation,
a human mathematical referee or Lean verification. The new rank-query closure
construction and its full enumerator are NOT re-certified by this audit.**

## 1. Scope and outcome

The latest [rank-query compiler record](../research/RANK_QUERY_COMPILER.md)
explicitly leaves its transfer through the older C029/C031 work at that work's
previous evidence level. This review addresses that interface, including the
underlying characterization of arbitrary, possibly infinite tree models.
It does not introduce a new restricted witness search or assume that a supplied
scheme bound is globally complete.

The audited implication is:

> A total correct decision for binary terminal BorderAvoid, together with the
> effective constructions proved below, yields a total decision for normalized
> subtype entailment over arbitrary trees built from bottom and covariant binary
> product. No finite-tree, regular-input-tree or bounded-stack assumption is added.

The actual supplied-path model can be regular even when its tree is infinite.
The exact positive/negative transfer is proved in Section 8. C030's reverse
realization is also checked, but is not needed for this sufficiency implication.
The terminal-to-subtype reduction must not be used as a substitute for the
subtype-to-terminal direction.

Primary repository entry points reviewed: [original characterization](../REVIEW.md),
[denials and continuations](2026-09-04-denials-and-continuations.md),
[summary absorption](2026-09-04-summary-absorption.md), and
[terminal realization and C031](2026-09-05-terminal-realization.md).
Existing authorship, claim scopes, counterexamples and evidence levels remain.

## 2. Normalization and arbitrary trees

Let Sigma={0,1}. For a type tree t, write X(t) for its finite addresses labelled
by product. These sets are prefix closed. Conversely every prefix-closed subset
X of Sigma* determines a unique possibly infinite tree: each address in X is a
product, and each required child outside X is bottom. The empty set is bottom;
Sigma* is the infinite full binary tree, without introducing a top constructor.

The covariant order is exactly inclusion of product-node sets. Products satisfy

    X(u x v) = {epsilon} union 0 X(u) union 1 X(v).

These equalities do not assume finiteness or regularity. A failed inclusion has
a finite address pi in its set difference, even if the trees are infinite.

Finite expressions can be named conservatively. Name bottom by b<=bottom.
For every compound subexpression u x v introduce z with BOTH constraints
u' x v' <= z and z <= u' x v', where the children have already been named.
Replace constraints and the query by their names. Induction on the finite
syntax shows that every original valuation has an extension satisfying the
naming equations and every extended valuation gives precisely those meanings.
This is an extension/restriction of valuations, not a finite-tree approximation.

The normalized forms are a<=b, a<=b x c, b x c<=a, and a<=bottom. The propagation
machine W has configurations (variable,word), stack top at the LEFT. Its rules
are respectively epsilon edges, pops, pushes, and prohibitions. A lower product
also forces its target's empty address. Write BF for these forced roots and D
for the denied variables. Every push TARGET is in BF.

## 3. Least closure is an actual model, including all prefixes

For a finite address pi proposed to separate alpha from beta, let

    Seeds_pi = {(f,epsilon):f in BF}
               union {(alpha,u):u is a prefix of pi},
    M_pi = Post_W*(Seeds_pi).

Reachability acts on membership facts, so M_pi is contained in every model
containing (alpha,pi). Indeed that model contains all alpha-prefix seeds by
prefix closure, all forced roots, and all their propagated consequences.

It remains to check that M_pi itself is a family of trees. A simultaneous
one-step closure of prefix-closed sets remains prefix closed:

* an epsilon rule transfers prefixes along with the word;
* a pop of a transfers each prefix v of its output because av is a prefix
  of its input and is popped by the same rule;
* a push of a transfers each nonempty prefix av from the corresponding input
  prefix v. Its additional empty prefix is present because the push target is
  forced in BF.

The seed sets are prefix closed, so induction and union over finite derivation
lengths prove prefix closure of M_pi. Rule closure gives every normalized
inequality; the only possible remaining violations are nonempty denied sets.
Thus M_pi is a model exactly when it avoids D. The forced-root closure M_0
is the least model candidate, and C is satisfiable iff M_0 avoids D.

It follows without any compactness premise that

    C does not entail alpha<=beta
    iff for some finite pi, M_pi avoids D and (beta,pi) is absent from M_pi.

The forward direction takes pi from an arbitrary countermodel and uses the
containment above. The reverse direction uses M_pi itself. Quantifying over
regular countermodels is therefore sufficient once their effective regularity
is proved; replacing them by finite trees is not.

### Essential regression: an infinite model is not a finite model

The constraints x x b <= x and b<=bottom force epsilon in X(x) and closure under
prepending 0. Their least solution is X(x)=0*, X(b)=empty. It is regular and
infinite, and it refutes x<=b at epsilon. No finite X(x) can satisfy the lower
product, since it would have to contain 0^n for every n. Restricting to finite
assignments would make the constraints unsatisfiable and entailment vacuous.
The checker proves equality with the regular language 0* by full automata
inclusion, rather than testing a list of long paths.

All alpha-prefix seeds also matter for separation, not just for presentation.
With x x b<=y and b<=bottom, seeding only (x,0) and the forced (y,epsilon) fails
to derive (y,0); seeding the required (x,epsilon) derives it immediately.
The former closure is not prefix closed and cannot be a tree countermodel.
This is retained as an explicit rejected regression.

## 4. Independent finite construction of exact reachability

The new checker does not call the original P-automaton saturation to construct
its reference languages. It first computes the least balanced relation E on
control pairs with these productions:

    E(p,p);
    E(p,q) for an epsilon rule p->q;
    E(p,q) and E(q,r) imply E(p,r);
    push_a(p,q), E(q,r), pop_a(r,s) imply E(p,s).

There are finitely many control pairs. Closing the relation terminates. Its
soundness is immediate by concatenating or enclosing runs. Completeness follows
by taking the first transition of a balanced nonempty run: an epsilon edge is
followed by another balanced run; a push must have a matching pop of its symbol,
with a balanced inner run and a balanced remainder. A pop cannot occur at an
empty baseline. This argument also holds above any fixed untouched stack tail.

Use E as epsilon edges and original pops as letter edges. A path labelled u
from p to q then recognizes exactly

    Pop_W(p,q) = {u:(p,u)->*_W(q,epsilon)}.

For completeness, decompose a consuming run at the times it consumes successive
symbols of the original stack. Before, between, and after those removals its
excursions above the current baseline are balanced. Conversely each such NFA
path lifts to a valid concrete stack computation.

### Minimum-stack factorization

For arbitrary configurations, not just subtype-derived ones,

    (p,u)->*_W(q,v)
    iff there are x,y,z,m with u=xz, v=yz,
         x in Pop_W(p,m), y in Pop_reverse(W)(q,m).                 (F)

For the forward implication choose a position of minimum stack height in the
finite run. Its stack z is an untouched suffix of both endpoints. Strip z from
both run pieces. Reverse the second piece. Neither piece ever reads below its
baseline, giving the two Pop relations. For the converse lift both runs above
z and concatenate after reversing the second. This permits arbitrary matched
push/pop excursions, not only monotone-height runs.

For a finite seed (p,u), enumerate its finitely many splits u=xz. For each
control m reached by the W-pop summary on x, attach the literal suffix z to
m in a reversed-W pop graph. Every attachment uses fresh NON-control nodes and
ends in one accepting sink. Starting this graph at q recognizes exactly the
possible v in (F). Union the attachments for all seeds. In particular M_0 and
M_pi are effectively regular at every variable, with no depth cutoff.

This directly proves the regularity needed by the bridge. The classical
P-automaton route is contextual background, not an additional unproved premise
of this oracle. See Bouajjani, Esparza and Maler, *Reachability Analysis of
Pushdown Automata: Application to Model-Checking*, CONCUR 1997,
DOI 10.1007/3-540-63141-0_10; the authors' publication entry is
https://archive.model.in.tum.de/um/bibdb/info/esparza.BEM97.shtml.html .

## 5. Ordered cut pairs, safety and the finite summary instance

Define for prefixes u of pi

    B(u) = {m:u in Pop_W(alpha,m)},
    A(u) = {m:u in Pop_reverse(W)(beta,m)}.

Forced beta membership at pi is exactly A(pi) intersect BF nonempty.
For membership propagated from an alpha-prefix seed, use (F) with that prefix
as u and pi as v. Write x=pi[:i], y=pi[:j], z=pi[j:]. Since the seed xz is a
prefix of pi, i<=j and pi[j:] is a prefix of pi[i:]. Conversely any such cuts
and a member of B(pi[:i]) intersect A(pi[:j]) provide the prefix seed and a
concrete propagation to (beta,pi). Therefore seed-derived beta membership is
exactly the existence of

    0<=i<=j<=|pi|,
    pi[j:] prefix-of pi[i:],
    B(pi[:i]) intersect A(pi[:j]) nonempty.                         (G)

Order is essential; no symmetry of G is assumed. The case i=j checks a diagonal
flag, and j=|pi| checks the empty terminal suffix. Neither may be discarded.
The same finite word pi fixes every cut and both summaries.

Denial safety can be recognized directly by a finite predecessor NFA whose
denied controls accept EVERY residual stack, as `summary_bridge.py` does.
Every alpha-prefix must avoid that NFA's accepted language. This is exact even
without the simplified empty-stack-denial lemma.

The simplified test used by the independent cut oracle is valid after the
satisfiability guard. If a prefix seed reaches a denial at nonempty residual
stack, take the minimum height of that run. If the endpoint is at that minimum,
strip its untouched tail to get a shorter prefix reaching the denial at empty
stack. Otherwise, after the LAST visit to the minimum, the next push has a
forced target f in BF. Its bottom symbol and underlying stack are never popped.
Strip that entire fixed tail to obtain a denial reachable from (f,epsilon),
contradicting satisfiability. Thus it suffices to exclude B(u) intersect D for
all prefixes u, but only with this guard. The actual implementation uses the
stronger direct predecessor language instead.

Determinize the W pop summary, reversed pop summary, and denial predecessor
NFA together, retaining empty subsets. The state reached after u records
B(u), A(u), and the denial subset. Mark finals by A(u) disjoint BF, mark Bad
using the denial NFA, and flag (c_i,c_j) by B_i intersect A_j nonempty.
This is a finite total binary deterministic automaton I_C. Under satisfiability,
its witnesses are exactly the finite separating paths from Section 3.

## 6. Why actual summaries absorb finality

The only letter edges of the reversed pop summary are reversed-W POP rules,
whose sources are forward-W PUSH targets, hence members of BF. Saturation adds
only epsilon edges; it does not introduce new letter-source controls.
Every subset A(u) is already epsilon closed. If A(u) avoids BF, it has no
outgoing letter edge. Consequently

    A(u a)=empty for every letter a,

and A remains empty after every positive extension. Every positive successor
of a final summary is therefore final with an EMPTY incoming flag column.
This statement is checked at the actual summary construction, not postulated
for arbitrary abstract automata.

For any annotated automaton satisfying this absorption property, call a state
safe when it is neither Bad nor diagonally flagged. Every safe extension of a
witness is again a witness. A newly alleged violation with target before or at
the old endpoint restricts to an old violation. A target strictly beyond the
old endpoint has an empty incoming flag column. Unsafe new states cannot be
ignored: their diagonal or Bad failures are precisely why safety is required.

## 7. Audit of C029: infinite safe extensions have an effective decision

Let Z be the final states with empty incoming columns. Its safe part is closed
under safe transitions. A witness with an infinite safe continuation can be
extended one step into Z, unless it is already there. Hence it suffices to find
some safe prefix ending in Z with an infinite safe continuation that eventually
becomes a witness. The prefix need not itself be a witness.

### Fixed prefix: only finitely many periodic continuations can obstruct it

Fix such a prefix u of length n. No future target cut is flagged. Every active
proper pair (i,j), i<j<n, that currently matches can remain matching forever
under exactly one infinite extension. Its gap d=j-i imposes periodicity and
the extension is the correctly rotated repetition of u[i:j]. Pairs already
mismatching can never recover. There are finitely many active pairs. A finite
continuation succeeds exactly when it is no longer a prefix of any of these
rays. Distinct flag pairs with identical rays may safely be merged.

Thus an infinite safe continuation yields some finite witnessing prefix iff
it differs from EACH active ray. This is not an interchange of an infinite
conjunction and a finite existential: the ray set is finite and the maximum
of their individual first mismatch positions is finite.

### Branching case

Restrict Z to vertices with infinite safe futures. If a reachable cycle vertex
has two available labelled exits in this restriction, choose a simple return
word v starting with a and another exit b!=a. For a fixed prefix u to that
vertex the tails v^j b, j=0,...,s, are pairwise prefix-incomparable, where s is
the number of active rays. Each ray has at most one of these tails as a prefix.
One of the s+1 tails therefore breaks every ray. Its endpoint still has an
infinite safe future by the restriction. This proves the constructive YES case
without invoking the existence of an aperiodic infinite word.

### Nonbranching case

If the preceding certificate is absent, every reachable cyclic vertex of the
restricted Z graph has only one available labelled outgoing edge. Every infinite
continuation is consequently a simple finite stem followed by a simple cycle:
a cyclic vertex cannot have an exit to a different infinite continuation.
Enumerating the simple prefixes up to the first repeated vertex exhausts these
lassos. A lasso whose label sequence is not purely periodic cannot equal an
active ray, so any safe prefix to its start can be extended to a witness.

For a purely periodic lasso with primitive period p of length d, the prefix
language needing examination is regular by the following explicit invariant.
Choose its endpoint phase o modulo d. During a scan, retain the current state,
length modulo d, and for each residue the set of states at cuts in the maximal
suffix agreeing with the absolute pattern p[(position-o) mod d]. Retain a
conflict bit for any ordered flagged pair in that suffix at equal residues.
On a mismatching letter discard all earlier cuts and the conflict bit; on a
matching letter add the new cut and check its incoming flagged pairs in the
matching residue bucket.

At the desired endpoint, require phase o and no conflict. A persistent flagged
comparison under p^omega has gap divisible by d: a shift preserving the infinite
primitive p-periodic sequence must be a multiple of d (otherwise its modular
orbits give a smaller period). Its two cuts lie in the recorded suffix and the
same residue bucket. Conversely each recorded conflict supplies a matching pair
that remains equal under the extension. The finite monitor is therefore exact.
Enumerate d possible endpoint phases and exhaust the finite reachable monitor
graph for each. This is the invariant implemented by `monitor_step` and
`periodic_prefix_search`; only the latter performs the initial-safety guard.

These cases exhaust infinite continuations. A default resource cap in the code
can return UNKNOWN; it does not change the finiteness of the mathematical
construction or authorize treating a cap as NO. C029 answers only the infinite-
continuation question, not the terminal remainder.

## 8. C031 and the end-to-end implication

From an absorbing I remove Bad and diagonal-flagged states and transitions
incident to them. Keep as accepting only safe ORIGINAL final states with no
remaining outgoing transition. Call the resulting binary terminal instance J.
No positive-length marker is appended and the flag order is unchanged.

Every witness of J is a witness of I: J only removes transitions, acceptance
choices and unsafe states, and its retained runs are the same original runs.
Conversely let w be a witness of I. If its endpoint admits an infinite safe
path, C029 covers it. Otherwise the safe graph reachable from that endpoint
has no cycle; a reachable cycle would itself give an infinite continuation.
Follow a shortest path to a sink, of length at most k-1. Absorption and safe
extension keep the extended word a witness and its endpoint an original final.
The endpoint is a safe sink, hence accepting in J. Therefore

    Witness(I) nonempty
    iff InfiniteWitnessContinuation(I)
        OR Witness(J) nonempty.                                  (T)

For a normalized subtype system first decide satisfiability. An unsatisfiable
system entails every query, so no summary-construction exception is interpreted
as non-entailment. Otherwise construct I_C from Section 5, use its established
absorption from Section 6, decide C029, and apply a terminal decider to J when
needed. Equations (G) and (T) prove the exact end-to-end transfer.

This discharges the older semantic TRANSFER implication at ordinary-proof
review level; the premise that the proposed rank-query terminal decider is
correct remains its own mathematical review obligation. C030 is unnecessary
for this direction. It establishes the reverse expressiveness statement and
is checked separately below.

## 9. C030 reverse realization sanity check

For a k-state binary terminal instance, introduce a_q, v_q and b. Set b<=bottom;
put an upper product on every a_q using transition successors and b for missing
edges; put the corresponding lower product into v_q ONLY for q not final; add
a_p<=v_q for each flag and a_q<=bottom for Bad states. Query a_start<=v_start.

Forward pushes stay within the v-copy, where there are no pop rules. Reversed
pushes stay within the a-copy, where there are no reversed pop rules. Hence no
push creates an extra balanced cross-copy summary. On a defined word ending
at q the two summary subsets are exactly

    B={a_q} union {v_t:(q,t) in G},
    A={v_q} union {a_p:(p,q) in G}.

Their intersection tests the same ORDERED flag. Forced roots are precisely the
nonfinal v-controls. Missing a-transitions enter denied b. The construction is
satisfiable by taking every a and b bottom and the least lower-product v-model,
which may be infinite. These facts prove word preservation, including Bad,
empty-suffix and diagonal cases. Omitting lower products at finals is exactly
why terminality is required. No reverse theorem for nonterminal-final abstract
inputs is inferred.

## 10. Evidence, reproducibility and limits

The checker is [check_semantic_bridge_review.py](../experiments/check_semantic_bridge_review.py).
Its new reference reachability implementation uses the grammar and factorization
in Section 4, not an imported call to either original saturation implementation.
The code separately checks prefix closure, denials and product inclusions by
full regular-language inclusion. With `--repository` it refuses to run if any
of six reviewed dependency blob hashes changed.

The local self-contained run compares 244 entire no-push reachability languages
with their completely enumerated finite closures; checks 1,200 supplied-path
canonical/ordered-cut equivalences; and verifies 396 positive regular models at
all depths. Eighty forced-root closures are checked for prefix closure. The
infinite-spine, missing-prefix, unsatisfiable forced-root and empty-query cases
are explicit regressions. These are finite corpora, not an all-instance proof.

The repository run compares complete Pop and Post languages with the original
implementations by finite subset-product exhaustion. It also audits the actual
summary and terminal-realization interfaces, checks the periodic monitor against
literal ordered pairs, and compares C029 with a complete all-length oracle on
unique-labelled-trajectory automata. The latter class is narrow: it does not
constitute an independent general C029 solver. C031 tests distinguish safe
sinks from endpoints with reachable cycles.

Commands:

```sh
python3 experiments/check_semantic_bridge_review.py --output /tmp/semantic-local.json
python3 experiments/check_semantic_bridge_review.py --repository --output /tmp/semantic-full.json
```

The first audit-branch workflow at commit
`5ae17b9087ee5ed3f5795b23b516b732134f6ca2` passed and replayed byte-for-byte.
Its repository run checked 1,518 complete Pop languages and 227 complete Post
languages (9,762 reachable inclusion-product states in total), 660 supplied
summary words, 2,480 C030 realization paths and 80 satisfiable realizations.
It checked 29,890 literal periodic-monitor cases, 21,260 active-ray phases,
320 complete unique-trajectory existence oracles and 32 finite-only safe-sink
extensions. Nineteen returned legacy regular models were checked at all depths;
the counter name `legacy_infinite_model_certificates` denotes a representation
allowing infinity, not a claim that all nineteen models are infinite.
The explicit 0* fixture is the independently verified infinite model.

[Saved executed results](../results/semantic-bridge-review.json) include the exact
six dependency blob hashes. The source itself is unchanged between local checks
and this remote execution. The final integration workflow compares its freshly
generated JSON with the saved result. Read that workflow's actual status before
claiming success on a different integrated revision. A successful job is implementation evidence, not a theorem-status vote.
No rank-query source was modified. This audit does not certify a full general
string/compiler enumerator, resource-unbounded host behavior, or every surface
syntax parser. The naming translation in Section 2 is a mathematical construction,
not a claim that a general parser was implemented or tested here. Earlier
candidate review, constructive proof, and external referee work remain distinct.

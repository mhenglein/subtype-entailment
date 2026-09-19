# Finite-expression normalization is a conservative definitional extension

Date: 2026-09-19.
Actor/session: ChatGPT `finite-expression-normalization-advisory-20260919`.
Related work: A010/A018; the finite-syntax obligation in #31; tracking #34; integration #37.

## Status, provenance, and scope

**Result:** a complete ordinary mathematical proof of a total normalization from finite expressions over variables, bottom, and binary covariant product to the existing four normalized clause forms. It preserves original valuations by a unique definitional extension, preserves entailment in both directions, and preserves each exact separating address.

**Evidence:** WRITTEN PROOF in this note; same-session mathematical readback. Independent review and kernel verification of the proposed normalizer remain pending. The Lean declarations below are proposals, not an implemented or compiled module. All example/test expectations below are mathematical arguments, not executed regression results. No Lean build, kernel replay, Python experiment, or full repository suite was run for the original investigation or this documentation-only publication.

**Original inspected snapshot:** `064fc7306b679bf607b91e7d8de259823f200c62`, main when the investigation began; commit timestamp 2026-09-19 13:22:38 UTC.

**Publication base:** `e1e8f635f0374d5c8112c8ee25c4220fc10198be`, freshly read from main before branch creation. The relevant `TreeSemantics` normalized constructors and semantic signatures were read back at this base; its file blob is `ead23728e922fa57c8b8c846129086f4f7aaa435`.

Sources read for the original investigation, pinned rather than silently replaced by later main:

- [Problem and notation](https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/research/problem.md).
- [STATE: current-frontier sections](https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/STATE.md).
- [Claims ledger: relevant semantics, bridge, and normalization entries](https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/research/claims.md).
- [Complete TreeSemantics source](https://github.com/mhenglein/subtail/blob/064fc7306b679bf607b91e7d8de259823f200c62/lean/Subtail/TreeSemantics.lean).

Publication coordination: [scope in #31](https://github.com/mhenglein/subtail/issues/31#issuecomment-5742582198) and [notice in #37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5742584780). The owner first requested a read-only advisory and subsequently explicitly requested publication of its findings. Only this new note is owned by the publication scope. No existing proof, interface, STATE/claims/approach ledger, import aggregator, workflow, toolchain, main ref, or another worker's files are modified by this contribution. Proposed canonical-index wording is supplied below for serialized integration.

At the original snapshot, finite-expression normalization was explicitly listed separately from C029 and final executable composition. This note discharges the ordinary mathematical normalization argument only; it neither completes C029 nor claims that Problem 1.7 or the full executable composition has been checked. Conservative naming was already an intended stage-6 obligation; no novelty or priority claim for the technique is made.

## 1. Semantic setting and exact input

Let `Word = {0,1}*`. A type is a prefix-closed set of finite addresses labelled by product. Let T be the collection of ALL such sets, not merely finite or regular ones. Define

- bottom = the empty set;
- A × B = {epsilon} union {0w : w in A} union {1w : w in B};
- A <= B iff A is a subset of B.

These are the definitions of `TreeSemantics.Tree`, `bottom`, `product`, and `Below`. The product root is always present: bottom × bottom is not bottom. No top constructor is introduced. The existence of the full infinite binary tree as a greatest semantic value is immaterial to the construction.

Fix a finite declared original variable set V, including all variables in the premises and query, and any other original variables whose identities are to be preserved. In particular, do not derive V solely from premise occurrences and accidentally omit query-only variables. For the existing Lean representation take V = Fin n.

Expressions are FINITE syntax trees:

    e ::= var x | bottom | e × e,   x in V.

For an arbitrary valuation rho : V -> T, define evaluation by recursion on expression syntax:

    [[x]]rho       = rho(x)
    [[bottom]]rho  = bottom
    [[u × v]]rho   = [[u]]rho × [[v]]rho.

Values rho(x) may be arbitrary infinite, nonregular trees. Evaluation performs no recursion through those values. A finite expression with infinite variable values is not itself required to denote a finite or regular tree.

Write the finite premise list as

    Gamma = [s_1 <= t_1, ..., s_m <= t_m].

Its model relation is conjunction of the evaluated inclusions. We allow a finite compound query s <= t for a stronger interface. Problem 1.7's original query alpha <= beta is the special case s = var alpha, t = var beta. If original variable names have a larger effective ambient domain, enumerate the finite declared support and retain its name-to-index injection; variables outside the support are untouched by the corresponding disjoint-extension construction.

## 2. Exact total construction

### 2.1 Forest and fresh allocation

Form a syntax forest containing both sides of every premise and both sides of the query. A repeated subtree appearing twice has two occurrences in this occurrence-based construction.

Let P be the number of product OCCURRENCES in the forest. Let B be 1 if bottom appears anywhere in it and 0 otherwise. Allocate exactly P+B fresh variables in a set disjoint from V.

If B=1 reserve one bottom proxy b_bottom, shared by all bottom occurrences. Allocate one distinct product proxy p_o for each product occurrence o. Do not use a textual prefix as a freshness proof: an original variable could already have that name.

For indexed variables use Fin(n+P+B). Embed every old index i<n with the SAME numeric value i, and allocate fresh indices in the interval [n,n+P+B). If B=1, b_bottom can be index n; assign product indices n+B+j, 0<=j<P, in fixed left-to-right postorder. No old index is reused or renumbered, and every index in the enlarged domain is accounted for.

### 2.2 Representatives

Associate a representative r(o) to each occurrence:

    r(var x)       = the embedded original x
    r(bottom)      = b_bottom
    r(o = u × v)   = p_o.

The bottom case is used only when B=1, so its representative always exists. Variable occurrences do not allocate new variables.

### 2.3 Definitional constraints D

If B=1 emit once:

    b_bottom <= bottom.

For every product occurrence o=(u × v), emit BOTH:

    p_o <= r(u) × r(v)
    r(u) × r(v) <= p_o.

Their order in the output list is immaterial to semantics; postorder is a deterministic implementation choice. The second inequality is essential because it forces the root and every product node required by the children. The first is essential because it forbids extra product nodes in the proxy.

A separate bottom <= b_bottom clause is unnecessary and is not an available normalized constructor: bottom is below every tree already. The single denial forces exact bottom.

### 2.4 Premises and output query

Replace each original premise by one variable inequality:

    r(s_i) <= r(t_i).

Let A be the list of these m inequalities and Delta = D ++ A. The output query is

    a <= c, where a=r(s), c=r(t).

**Do not add the output query to Delta.** Definitions for its subexpressions are allowed because they extend every original valuation; the queried comparison is not an assumption.

Every output clause is of one of the four existing forms:

    x <= y
    x <= y × z
    x × y <= z
    x <= bottom.

For alpha <= beta, r(alpha) and r(beta) are precisely the embedded original indices. There is no new proxy around either query variable. Thus the variable query is preserved, not merely replaced by an unrelated equisatisfiable test.

### 2.5 Totality and effective implementation

First count P and detect bottom in the finite forest. Then traverse the forest in fixed left-to-right postorder, emitting definitions into an accumulator and returning each root representative. All child representatives exist before a parent is emitted. Append the m premise root comparisons and return the two query representatives separately.

This terminates by recursion over finite syntax. It uses no satisfiability check, semantic tree equality test, model enumeration, infinite unfolding, occurs check, C029 solver, or bound on separating addresses. An implementation should use accumulators rather than repeated long list appends if it wants the linear syntax-operation bound below.

## 3. Exact theorem

Let (Delta,a,c) be the output for (Gamma,s,t), and let eta|V be restriction to the preserved original indices.

**Definition theorem.** Every valuation rho:V->T, regardless of whether it satisfies Gamma, has a unique extension rho_hat satisfying D. Every eta satisfying D satisfies, for every compiled occurrence o,

    eta(r(o)) = [[o]](eta|V).                       (R)

**Model theorem.** Every rho satisfying Gamma extends to rho_hat satisfying Delta, and every eta satisfying Delta restricts to eta|V satisfying Gamma. Extension and restriction are inverse bijections between the two model classes.

**Entailment theorem.**

    Gamma entails s <= t  iff  Delta entails a <= c. (E)

For the original variable query, this is

    Gamma entails alpha <= beta
      iff Delta entails embed(alpha) <= embed(beta).

The embedding preserves each original numeric index.

**Exact-address theorem.** For EVERY fixed finite address w,

    exists rho, rho models Gamma
                and w in [[s]]rho and w not in [[t]]rho
      iff
    exists eta, eta models Delta
                and w in eta(a) and w not in eta(c). (W)

No transformation of w is needed. The theorem preserves every separating address, not only the existence of some counterexample.

**Satisfiability corollary.** Gamma is satisfiable iff Delta is satisfiable. No consistency premise is imposed.

## 4. Complete ordinary proof

### 4.1 Canonical extension of every original valuation

Take any rho:V->T. Define rho_hat on the disjoint enlarged variable set by

    rho_hat(x)        = rho(x)                    for original x;
    rho_hat(b_bottom) = bottom                    when B=1;
    rho_hat(p_o)      = [[u × v]]rho               for o=(u × v).

The definition is unambiguous: original and fresh names are disjoint, every product occurrence has a unique proxy, and all bottom occurrences have the same semantic value. Evaluation is already defined for each finite original subexpression without consulting the fresh values.

For every occurrence o,

    rho_hat(r(o)) = [[o]]rho.                     (1)

This follows directly in the variable and bottom cases, and is the defining assignment to p_o in the product case.

The denial holds because rho_hat(b_bottom)=bottom. For a product occurrence o=(u × v), equation (1) gives

    rho_hat(p_o)
      = [[u × v]]rho
      = [[u]]rho × [[v]]rho
      = rho_hat(r(u)) × rho_hat(r(v)).

Therefore both defining inclusions hold by reflexivity. Hence rho_hat models D. Importantly, this construction works before assuming any original premise: D alone restricts no original valuation.

### 4.2 Representative correctness for every model of D

Take eta models D and put rho=eta|V. Prove (R) by structural induction on the occurrence o.

For a variable x, its representative is its embedded original index. Thus eta(r(x))=rho(x)=[[x]]rho.

For bottom, the denial gives eta(b_bottom) subseteq empty. The reverse inclusion is automatic, so eta(b_bottom)=empty=[[bottom]]rho.

For o=(u × v), both emitted constraints give

    eta(p_o) subseteq eta(r(u)) × eta(r(v)),
    eta(r(u)) × eta(r(v)) subseteq eta(p_o).

Antisymmetry of inclusion gives equality. The induction hypotheses for u and v then yield

    eta(p_o)
      = eta(r(u)) × eta(r(v))
      = [[u]]rho × [[v]]rho
      = [[u × v]]rho.

This completes the induction. It uses only finite syntax induction, inclusion antisymmetry, and the semantic definition of product.

It also proves uniqueness of rho_hat: an extension has prescribed original values, the bottom proxy is forced to bottom, and each product proxy is forced to the evaluation of its original subexpression. All output variables are among these. Thus every eta models D equals the canonical extension of eta|V, extension followed by restriction is the identity, and restriction followed by extension is the identity on models of D.

### 4.3 Original models extend to normalized models

Let rho models Gamma. Section 4.1 gives rho_hat models D. Every original premise gives

    [[s_i]]rho subseteq [[t_i]]rho.

Using (1), this is exactly rho_hat(r(s_i)) subseteq rho_hat(r(t_i)), the translated root premise. Consequently rho_hat models A as well as D, hence rho_hat models Delta.

### 4.4 Normalized models restrict to original models

Let eta models Delta and rho=eta|V. Since D is included in Delta, section 4.2 applies. Every translated root premise gives

    eta(r(s_i)) subseteq eta(r(t_i)).

Applying (R) to both sides gives [[s_i]]rho subseteq [[t_i]]rho. All original premises therefore hold, so rho models Gamma. Combining this with the uniqueness in section 4.2 proves the model bijection.

### 4.5 Entailment in both directions

Assume Gamma entails s<=t, and take any eta models Delta. By section 4.4, rho=eta|V models Gamma, so [[s]]rho subseteq [[t]]rho. By representative correctness this is eta(a) subseteq eta(c). Thus Delta entails a<=c.

Conversely assume Delta entails a<=c, and take any rho models Gamma. By section 4.3 its extension rho_hat models Delta. Therefore rho_hat(a) subseteq rho_hat(c), which by (1) is [[s]]rho subseteq [[t]]rho. Hence Gamma entails s<=t. This proves (E).

For (W), extend any original separating model or restrict any normalized separating model using the same constructions. Equations (1) and (R) preserve membership and nonmembership of the SAME w on both sides. This proves both implications for every fixed address.

For satisfiability, extension maps every original model to a normalized model, and restriction maps every normalized model to an original model. This proves the corollary. QED.

### 4.6 Boundary cases and what the argument does not assume

**Inconsistent premises:** neither implication presupposes a model. If Gamma has no model, Delta has no model; conversely likewise. Both entail every query vacuously. No special unsatisfiability branch is needed in normalization.

**Recursive constraints:** x × bottom <= x is allowed. The original value of x may need to be infinite. This is a constraint on a valuation, not an instruction to unfold a recursive syntax tree or reject an occurrence of x. Fresh definitions follow finite expression structure even if the overall constraint dependency graph has cycles.

**Arbitrary and nonregular values:** all original valuations are included, and original values are literally unchanged by extension. No compactness, finite-model property, regular-countermodel property, decidable-membership assumption, or witness-length bound is used.

**Compound query kept literally:** one can also retain s and t with original variables lifted into the larger domain. Their evaluations under eta equal the original evaluations under eta|V, by elementary expression induction. Thus

    Gamma entails s<=t
      iff Delta entails lifted(s)<=lifted(t)
      iff Delta entails a<=c.

The final variable query is only a way to match the existing `Entails` interface.

**No mathematical gap claimed:** the ordinary proof has no unresolved implication. This does not turn the unimplemented compiler into a checked Lean theorem. Actual allocation, indexing, emitted-clause membership, and proof integration remain formalization obligations.

## 5. Exact sizes and sharing

With P product occurrences, B in {0,1} indicating any bottom, and m original premises:

    fresh variables             = P+B
    enlarged variable count     = n+P+B
    definitional clauses |D|    = 2P+B
    translated premises |A|     = m
    total output clauses        = m+2P+B.

These are exact lengths of the specified LIST representation. Interpreting clauses as a set or removing duplicates only reduces the count. Every original premise is replaced by one root inequality; the additional definitional overhead is 2P+B. The query contributes its product/bottom syntax to P and B but contributes NO assumed comparison. A variable query contributes neither.

If S is the number of input syntax nodes, counting and accumulator-based postorder generation use O(S+m) elementary syntax operations and O(S+m) output space, treating index operations as unit-cost. This is not a claim about arbitrary-precision bit complexity, naive repeated list concatenation, or the cost of the eventual normalized decision procedure. Binary index encodings require O(log(n+P+B+1)) bits per reference; a corresponding straightforward encoding-aware bound includes that factor. A compact expression DAG should not be unfolded exponentially merely to use an occurrence count.

**Unshared repetitions:** two occurrences of x × bottom may get distinct proxies. By (R), both must denote the same tree, with no extra equality clause. This avoids any need for hashing or syntactic equality in the baseline normalizer.

**Optional sharing:** use one proxy per distinct syntactic product subexpression, or per product node in an already supplied acyclic expression DAG. Order the definitions topologically and repeat the proof in section 4.2 in that order. If there are P_shared such nodes, the counts become P_shared+B fresh variables and m+2P_shared+B clauses. Only syntax is shared; no semantic-equivalence decision is needed. Cycles in original constraints do not make this finite syntax DAG cyclic. A cyclic expression graph would be a different input language and is not silently admitted.

## 6. Existing Lean boundary and proposed interfaces

The inspected `Subtail.TreeSemantics` exposes:

```lean
inductive Constraint (n : Nat) where
  | leq (source target : Fin n)
  | upper (source left right : Fin n)
  | lower (left right target : Fin n)
  | denial (source : Fin n)
```

Its `Valuation n` is `Fin n → Tree`; `Holds`, `Models`, `Satisfiable`, and `Entails` have exactly the semantics used above. Note especially that the target of `.lower` comes LAST. Product definitions emit `.upper p l r` and `.lower l r p`.

A new module importing ONLY `Subtail.TreeSemantics` is sufficient for this front-end task. Do not change the existing definitions, and do not import C029 or the terminal compiler merely to prove normalization.

### 6.1 Proposed declarations: NOT COMPILED

The following is an interface sketch, not a source contribution or evidence that it elaborates against the pinned toolchain:

```lean
import Subtail.TreeSemantics

namespace Subtail.ExpressionNormalization

open Subtail.TreeSemantics

inductive Expr (n : Nat) where
  | var (x : Fin n)
  | bot
  | prod (left right : Expr n)
  deriving DecidableEq, Repr

def eval {n : Nat} (rho : Valuation n) : Expr n → Tree
  | .var x => rho x
  | .bot => bottom
  | .prod s t => product (eval rho s) (eval rho t)

abbrev Input (n : Nat) := List (Expr n × Expr n)

def ExprModels {n : Nat}
    (Gamma : Input n) (rho : Valuation n) : Prop :=
  ∀ c ∈ Gamma, Below (eval rho c.1) (eval rho c.2)

def ExprEntails {n : Nat}
    (Gamma : Input n) (s t : Expr n) : Prop :=
  ∀ rho, ExprModels Gamma rho →
    Below (eval rho s) (eval rho t)

structure Output (n : Nat) where
  extra : Nat
  definitions : List (Constraint (n + extra))
  premises : List (Constraint (n + extra))
  leftRoot : Fin (n + extra)
  rightRoot : Fin (n + extra)

def Output.constraints {n : Nat} (R : Output n) :=
  R.definitions ++ R.premises

-- Old indices keep their numeric values.
def restrict {n : Nat} (k : Nat)
    (eta : Valuation (n + k)) : Valuation n :=
  fun x => eta (Fin.castAdd k x)

end Subtail.ExpressionNormalization
```

The proposed `Fin.castAdd k` old-index embedding and `Fin.natAdd n` fresh-index embedding should be checked against the PINNED Lean toolchain before implementation. Their required mathematical contracts are simply `old(x).val=x.val` and `fresh(j).val=n+j`; explicit Fin constructors with the relevant inequalities are equally suitable. Do not use modular Fin addition to allocate variables. The original advisory's external Lean-documentation pointer was not an executed compatibility check and is not offered as such here.

### 6.2 Proposed theorem signatures: bodies intentionally omitted

The following block is SIGNATURE-ONLY DESIGN, not a compilable file with missing proofs promoted to results. Names are proposals rather than a claim of agreed interfaces or file ownership.

```text
-- In namespace Subtail.ExpressionNormalization:
variable {n : Nat}

def normalize
    (Gamma : Input n) (s t : Expr n) : Output n

def extend
    (Gamma : Input n) (s t : Expr n) (rho : Valuation n) :
    Valuation (n + (normalize Gamma s t).extra)

theorem restrict_extend
    (Gamma : Input n) (s t : Expr n) (rho : Valuation n) :
    restrict (normalize Gamma s t).extra
      (extend Gamma s t rho) = rho

theorem extend_models
    (Gamma : Input n) (s t : Expr n) (rho : Valuation n)
    (h : ExprModels Gamma rho) :
    Models (normalize Gamma s t).constraints
      (extend Gamma s t rho)

theorem restrict_models
    (Gamma : Input n) (s t : Expr n) :
    let R := normalize Gamma s t
    ∀ eta : Valuation (n + R.extra),
      Models R.constraints eta →
      ExprModels Gamma (restrict R.extra eta)

theorem roots_correct
    (Gamma : Input n) (s t : Expr n) :
    let R := normalize Gamma s t
    ∀ eta : Valuation (n + R.extra),
      Models R.definitions eta →
      eta R.leftRoot = eval (restrict R.extra eta) s ∧
      eta R.rightRoot = eval (restrict R.extra eta) t

theorem normalize_entails_iff
    (Gamma : Input n) (s t : Expr n) :
    let R := normalize Gamma s t
    ExprEntails Gamma s t ↔
      Entails R.constraints R.leftRoot R.rightRoot

theorem variable_query_preserved
    (Gamma : Input n) (alpha beta : Fin n) :
    let R := normalize Gamma (.var alpha) (.var beta)
    R.leftRoot = Fin.castAdd R.extra alpha ∧
    R.rightRoot = Fin.castAdd R.extra beta
```

Also prove the definitions-only extension theorem, uniqueness over a fixed restriction, the satisfiability equivalence, the exact-address equivalence, and the exact size identities. The main invariant must cover EVERY compiled occurrence, not just the two query roots. An occurrence certificate, a postorder table, or correctness proved alongside a structurally recursive compiler can connect original occurrences to representatives and emitted clauses.

For equality of the existing `Tree` structure, a small extensionality lemma converts equality of node predicates into tree equality, using proof irrelevance for prefix closure. Mutual `Below` gives pointwise equivalence and then predicate equality via propositional/function extensionality. Alternatively, formulate intermediate correctness by nodewise equivalence. No decidable tree equality is needed, and no classical choice is needed in executable normalization. Standard logical principles used to state extensional tree equality are not finite/regular-tree assumptions.

## 7. Eight adversarial example groups

**Status for this entire section: mathematical examples / proposed regressions, NOT EXECUTED TESTS.** They should be retained even after formalization so future implementations do not quietly weaken the theorem.

### A. Nested products and repeated subexpressions

Input premise:

    (x × bottom) × (x × bottom) <= y.

Allocate b,p1,p2,p3. Output:

    b <= bottom
    p1 <= x × b;       x × b <= p1
    p2 <= x × b;       x × b <= p2
    p3 <= p1 × p2;     p1 × p2 <= p3
    p3 <= y.

Here P=3, B=1, m=1: four fresh variables and eight clauses. The first two subexpressions are separate occurrences but (R) forces p1=p2 semantically. The sharing variant could reuse one proxy, but sharing is not needed for correctness.

### B. Product is not bottom; an upper-only proxy is unsound

Input: bottom × bottom <= bottom.

Correct output:

    b <= bottom
    p <= b × b
    b × b <= p
    p <= b.

This is inconsistent. The lower definition forces epsilon in p, while p<=b and the denial forbid it. Deleting the lower definition makes the all-bottom valuation satisfy the remaining constraints, turning an inconsistent input into a satisfiable one. This tests the root as well as the direction of the generated clauses.

### C. A lower-only proxy can be too large

Input: x <= bottom × bottom.

The erroneous output without the upper definition is

    b <= bottom
    b × b <= p
    x <= p.

Set b=bottom and p=x=(bottom × bottom) × bottom. All erroneous clauses hold, but the original inequality fails at address 0. The upper definition is exactly what excludes the extra node. One-sided proxy definitions are therefore not an adequate replacement for this conservative model-bijection construction.

### D. Fresh-name collision changes an original query

Input Gamma={bottom<=x}; query b<=x, where b is an ORIGINAL variable.

The query is not entailed: choose x=bottom and b=bottom × bottom. An incorrect allocator that reuses original b as the bottom proxy adds b<=bottom, making b<=x entailed. The disjoint allocation invariant excludes this. Include original names that look like generated names in a named-variable front end.

### E. Infinite models must not be rejected

Input Gamma={x × bottom<=x}; query x<=bottom.

Let X={0^j : j>=0}. This is a prefix-closed infinite product set and X × bottom = X, so it satisfies the premise and falsifies the query at epsilon.

Every model of the premise has epsilon in x; if w is in x, then 0w is in x. Thus it has 0^j for every j and cannot be a finite tree. A finite-tree-only semantics would incorrectly make the query vacuously true. The inspected TreeSemantics source already contains `zeroSpine`, `zeroSpine_lower`, and `zeroSpine_unbounded` as useful related semantic regressions. Their presence is source evidence, not a fresh execution of them in this investigation.

### F. Query definitions are not the query assumption

Take empty Gamma and query bottom × bottom<=bottom.

Correct normalized premises:

    b <= bottom
    p <= b × b
    b × b <= p.

Query: p<=b. These premises are satisfiable, and the query is false at epsilon. Adding p<=b as a premise instead makes the system inconsistent and the entailment true. A regression should explicitly check separation at the empty address.

### G. Empty input, query-only variables, and zero original variables

For empty Gamma and distinct original query variables alpha,beta, the compiler adds no variables or clauses and leaves the non-entailment alpha<=beta unchanged. Choose alpha=bottom × bottom, beta=bottom. If alpha=beta instead, the query is entailed; include both diagonal and off-diagonal query cases. Query-only variables must be in the declared domain even when the premise list mentions no variable.

With n=0, empty Gamma, and query bottom<=bottom, allocate only b_bottom, emit its denial, and query b_bottom<=b_bottom. This exercises Fin 0 without fabricating an original variable. P=0, B=1, m=0 gives exactly one added variable and one clause.

### H. Nonregular valuations are retained, not only regular countermodels

For the tautological premise bottom<=x, let

    X = {0^j : j>=0} union {0^(k^2)1 : k>=0}.

This is prefix-closed: prefixes of any terminal 1 word are among the all-zero spine. It is nonregular. If a finite automaton recognized X, whether it accepted 0^j1 would be eventually periodic in j because its states along 0^j are eventually periodic. The square positions are not eventually periodic: for any proposed positive period d, choose k large enough that k^2+d lies strictly between consecutive squares beyond the proposed threshold. Acceptance at k^2 and k^2+d would have to agree but does not.

The extension preserves the original value X exactly. No claim that regular models suffice is needed anywhere in the normalization proof.

## 8. Follow-up and acceptance plan

The next normalization-specific contribution should be a small, separately coordinated module proving the compiler invariant and then the public equivalence theorems. It need not wait for C029 and must not alter that worker's interfaces. Suggested progression:

1. Have a different session read back the ordinary theorem, especially freshness, both proxy inequalities, query definitions versus assumptions, and the arbitrary-tree quantifiers. This is review of a completed argument, not a request to weaken it to satisfiable or regular inputs.
2. Implement the occurrence-based normalizer first, with explicit declared n, old-index preservation, postorder allocation, and a reusable representative-correctness invariant. Use its model theorem to derive entailment and exact-address preservation, including n=0 and inconsistent premises. Prove the exact P+B and m+2P+B list-size statements.
3. Turn A-H into independent regression fixtures. Use complete finite address sets for finite examples without truncating products after evaluation. Use the explicit infinite-tree argument for E, and retain H as a semantic quantifier test rather than claiming a finite enumerator exhausts arbitrary trees. Add deterministic generated syntax tests that evaluate expressions independently of emitted clauses. Finite agreement is supporting evidence, not the proof of the theorem.
4. Check the new module with the pinned Lean toolchain, kernel replay, dependency/axiom audit, and a separate statement readback. Verify the runtime normalizer does not depend on noncomputable choice. Record exact source SHAs and commands actually run; do not relabel these proposed steps as existing evidence.
5. Only after an independently checked normalized entailment decision exists, compose it with `normalize_entails_iff` to obtain a finite-expression front end. That composition still requires the normalized backend theorem. The clause-weight U/F question is separate and need not become a new dependency of syntax normalization or qualitative decision.

These are recommendations and acceptance criteria, not launched workers, assigned ownership, background tasks, or a claim of integration. Optional DAG sharing should come after the simple occurrence version unless the actual input is already a DAG; it is an optimization with its own representation invariant, not a missing semantic ingredient.

## 9. Proposed canonical-index wording for the integrator

Do not mark syntax normalization LEAN or update the full-problem acceptance status based on this note alone. No new C/E/Q identifier is allocated here; the integrator can place the result under the existing A010/A018 and #31 obligations or allocate a collision-free stable record after checking the live ledger.

Suggested STATE / A018 entry:

> A complete written finite-expression normalization proof is recorded in `notes/2026-09-19-finite-expression-normalization-advisory.md`. For arbitrary possibly infinite product-address trees, collision-free conservative naming gives a model bijection, preserves the original variable query and each separating address, and uses P+B fresh variables and m+2P+B normalized clauses (P product occurrences, B indicating bottom). It handles inconsistent inputs without a satisfiability premise. Status: WRITTEN PROOF; independent review, executable implementation, and Lean verification pending. C029 and final executable composition remain separate obligations. The proposed interfaces and adversarial fixtures have not been compiled or executed by this contribution.

Suggested claims-record scope: model-preserving normalization of FINITE syntax into the four existing forms, not an infinite-expression parser, not a finite-tree or regular-tree reduction, not an independent decision theorem. Link this note and the existing TreeSemantics definitions. Retain the pending formalization status until the actual module, kernel evidence, and cross-session readback are integrated.

## 10. Evidence handoff summary

- Ordinary construction and all theorem implications: supplied in sections 1-5.
- Existing normalized source interface: inspected at the original snapshot and relevant signatures read back at the publication base.
- Proposed Lean implementation: NOT IMPLEMENTED / NOT COMPILED.
- Adversarial fixtures: mathematical expected outcomes supplied; NOT EXECUTED.
- Lean build, kernel replay, axiom audit, Python suite, full repository/index checks: NOT RUN by this contribution unless a later PR handoff records a separately identified actual run.
- GitHub publication and readback details: to be recorded in the associated PR / #31 handoff using the resulting immutable commit SHA, rather than self-referencing an unknown commit in this file.
- Scope: one new note only; no shared-file, C029, toolchain, proof-interface, or main changes. Main integration and canonical-ledger synchronization remain serialized through #37.

The reusable conclusion is exact: finite syntax normalization is a conservative definitional extension over the existing arbitrary-tree semantics. Its ordinary proof is complete here; the remaining normalization work is implementation and formal verification of that construction, not an unresolved semantic implication.

# Referee brief: the promotion-preimage (closure) lemma of the rank-query candidate

Date: 2026-09-18. Prepared by an integrator session (issue #25) from the
existing records; no new mathematics. Purpose: give an external human referee
one self-contained page stating exactly what must be checked, and give the
formalizer the statement to pin in Lean before proving it. Sources:
[candidate proof](2026-09-15-candidate-rank-query-decision.md) (Sections 3–7,
Lemma 4), [closure proof and bound](2026-09-17-rank-query-closure-audit.md)
(Sections 1–6), [closure review](2026-09-17-rank-query-independent-review.md).
Where this brief and those notes differ, the notes are authoritative.

## 0. What is being asked, and what is not

Asked: decide whether the **Closure Lemma** of Section 3 below is true as
stated, or exhibit a counterexample. It is the only step of the candidate
argument that neither Lean nor a differential oracle covers, and both existing
audits were informed by the author's own argument.

Not asked: the terminal rank bound and milestone facts (stages 1–2, kernel-
checked in Lean); the first-return graph identities (stage 3, being formalized
and independently replayed on 25,966 literal first returns); the C029/C031
semantic bridge (stage 6, audited separately); practicality of the bound.

## 1. Objects

**Instance.** `I=(Q,delta,s,F,Bad,G)`: a finite partial deterministic automaton
over `{0,1}`, `k=|Q|>=1`, no transition leaves any `f in F` (terminality),
`G subseteq Q x Q` the forbidden ordered pairs ("flags"), `Bad subseteq Q`.

**Witness.** A word `w` with defined run `c(0..N)`, `c(N) in F`, no `c(i) in Bad`,
such that for all `0<=i<=j<=N`: `w[j:] prefix of w[i:]` implies `(c(i),c(j)) notin G`.
Diagonal pairs `i=j`, the empty suffix `j=N`, and the empty word are included.

**Reversal and references.** Put `rho=reverse(w)`, `r_j=c(N-j)`. A *safe labelled
reference* is `B=b_0..b_(m-1)`, `m>=1`, with states `r_0..r_m`, `r_0` a safe
terminal final, `delta(r_(j+1),b_j)=r_j`, and every border-chain test through
`m` safe. Its last state need not be `s`. With `col(q)={p:(p,q) in G}` and
`pi(j)` the longest proper border of `B[:j]`, the *mask* is
`M_0=col(r_0)`, `M_j=col(r_j) cup M_(pi(j))`.

**Prefix graph `P(B)`.** Vertices `0..m`. Edge labels `F,S,K0,K1`: `F(i)=pi(i)`;
`S(i)=i+1` for `i<m`; `K_a(i)` is the longest-prefix update of `B[:i]` on
appending `a` (at `i=m` the update starts from `pi(m)`). Vertex colour
`(r_i, M_i, next_i, root_i, end_i)` in the finite alphabet
`Q x 2^Q x {0,1,END} x Bool x Bool`; no numeric position is part of a colour.

**Observer.** An epsilon-free finite-state path automaton: finite control set,
initial/final control subsets, a permitted-colour predicate per control, and a
finite transition relation `(control, source_colour, edge_label, target_colour,
next_control)`. Size `s` = number of controls.

**Query grammar `Qry`.** A clause is: finitely many existential vertex
variables; unary finite-colour tests; equalities and disequalities between
variables; path atoms `Path_O(x,y)` "some directed path from `x` to `y` is
accepted by observer `O`". A query is a finite union of clauses. **Excluded**:
inverse edges, negative reachability, equality of path labels, set
quantification, any string variable. Weight
`T = max(2, 1+v+a+sum_i s_i)` (variables, atoms, observer sizes).

**First-return extension.** `C = B a_1..a_L` (`L>=1`) is a *safe first-return
extension* of `B` when the old-graph cursors `h_0=F(m)`, `h_i=K_(a_i)(h_(i-1))`
satisfy `h_i != m` for `i<L`, `h_L=m`, and the chosen reverse states
`q_0=r_m`, `delta(q_i,a_i)=q_(i-1)` avoid `Bad`, their diagonal flag, and
`M_(h_i)`. Then `P(C)` is `P(B)` with: old endpoint `m` recoloured
(`next=a_1`, `end=false`) and its `K_(a_1)` edge redirected to the first fresh
vertex; an `S` edge `m -> m+1`; fresh vertices `m+1..m+L` with
`F(m+i)=h_i`, `S` and `K_(a_(i+1))` forward, the other `K_b` to old `K_b(h_i)`;
at the fresh endpoint `F -> m`, `K_(a_1)` wraps to `m+1` (a self-loop when
`L=1`), other `K_b` to old `K_b(m)`. *Consequence used everywhere:* the only
edges from old vertices into the fresh part land on `m+1`; fresh-to-fresh
edges are forward-adjacent except the endpoint wrap to `m+1`.

## 2. The finishing query and the algorithm that depends on the lemma

`Finish_I`: three variables, two path atoms, `k+2` observer controls: one `F`
edge from the graph endpoint to its proper failure parent, then a `K0/K1`
observer that carries the actual original state, forbids `End`, checks the new
state's `Bad`/diagonal/mask obligations, and accepts at `s` (empty path allowed
when the reference already ends at `s`). `P(B) |= Finish_I` iff `B` completes
to a witness with **no further promotion**.

Define `Phi_0=Finish_I`, `Phi_(h+1)=Phi_h or Pre_I(Phi_h)`. By stages 1–2 a
witness needs at most `k-2` promotions after its first letter, so
`Witness(I) != empty  iff  some safe one-letter reference satisfies Phi_(k-2)`.
The bound `F(k)` then follows by choosing shortest interval paths after the
diagram is fixed (closure note, Section 6).

## 3. The Closure Lemma (the object of review)

> **Closure Lemma (stage 4).** There is an effective map `Pre_I : Qry -> Qry`
> such that for every query `phi`, every safe labelled reference `B` (`m>=1`):
>
> `P(B) |= Pre_I(phi)`  **iff**  there exists a safe first-return extension
> `C` of `B` with `P(C) |= phi`.
>
> Moreover `Pre_I(phi)` is a finite union of clauses each of weight at most
> `U_k(T) = 64*k*T^(2T+2)` where `T` is the weight of `phi` (stage 5).

Construction (closure note, Sections 3–4). For a satisfying assignment on some
`P(C)` choose *product-simple* paths (no repeated (vertex, control) pair); each
atom then makes at most `s_i+1` forward excursions into the fresh strip, giving
at most `6T` *marks* (fresh variables, first/last fresh vertex, excursion
endpoints). A *diagram* records: old/fresh assignment of variables, the weak
order and coincidences of marks, observer controls at marks, portal edge
choices, guessed old-endpoint colour and first bit `a_1`. Each diagram compiles
to one clause: core pieces on the recoloured old graph; portal pieces as unary
predicates or single `K_b` edge atoms to KMP origins `z_t`; and, for each
physical interval between consecutive marks, **one** product observer with
control `(q, next, seen, t_1..t_b)` that generates the reverse run and lets
every active observer read the same emitted bit and the same two fresh colours.

### The four points a referee should try to break

1. **Joint compilation.** Preimages must be taken for the whole conjunction
   with one ordered mark set and one product per physical interval. Choosing a
   fresh reference per path atom is unsound. Check that no step silently
   re-introduces independent references, and that shared query endpoints and
   zero-length pieces are handled (closure review, Section 3).
2. **Single generator.** The delayed next bit, positive-length bit and `End`
   guard must force exactly one first-return `C` from any model of a compiled
   clause, including `L=1` and a return at the ultimate accepting cut.
3. **Expressibility of portals.** Entrance, wrap, `F` exits and mismatch exits
   from marks must be expressible with unary colour predicates and ordinary
   directed one-edge or path atoms, given that origins of distinct marks may
   coincide (they are KMP cursors, not positions).
4. **Self-application.** The output clause must satisfy the same grammar
   contract: finite colour maps, no hidden register, no reachability call
   inside a predicate, so that `Pre_I` can be applied to its own output and the
   weight bound composes (closure review, Section 3, "repeated compilation").

The known adversarial facts to keep in view: the single-entry hypothesis fails
if inverse failure edges are admitted (so any argument using reversed edges is
out of scope); two independently satisfiable word requirements can be jointly
unsatisfiable (the `S`-paths of length 2 and 3 fixture); the finite quotient of
references by endpoint, action, visited set and profile is false.

## 4. Proposed Lean interface for pinning the statement (not implemented)

Reusing `Subtail.Basic` (words, partial DFA, `Witness`) and the checked
`TerminalRank`/`RankMilestones` layers, the statement can be recorded as a
`Prop` without `sorry`:

```text
structure Colour (k) := (state : Fin k) (mask : Finset (Fin k)) (next : Option Bool) (root end_ : Bool)
def prefixGraph (I) (B : Reference I) : Graph (Colour k)          -- literal, executable
inductive Observer (k) ...                                          -- finite controls, table
inductive Query (k) ...                                             -- vars, colour tests, =/≠, Path atoms
def Sat (G : Graph (Colour k)) (φ : Query k) : Prop                 -- decidable on finite G
def weight : Query k → Nat
def FirstReturnExt (B C : Reference I) : Prop                       -- as in §1
def ClosureStatement (I) : Prop :=
  ∃ pre : Query k → Query k,
    (∀ φ B, Sat (prefixGraph I B) (pre φ) ↔ ∃ C, FirstReturnExt B C ∧ Sat (prefixGraph I C) φ)
    ∧ ∀ φ, clauseWeight (pre φ) ≤ 64 * k * (weight φ) ^ (2 * weight φ + 2)
```

Pinning `ClosureStatement` first, then instantiating `pre` with the compiler's
finite construction and proving the two directions separately, is the order
recommended in the Lean handoff. The Python compiler `rank_preimage.py` can
then be fuzzed against `Sat` by `native_decide` on small graphs.

## 5. Pointers

Candidate record: [RANK_QUERY_CANDIDATE.md](../research/RANK_QUERY_CANDIDATE.md);
compiler record: [RANK_QUERY_COMPILER.md](../research/RANK_QUERY_COMPILER.md);
claims entry: [C080](../research/claims.md#c080); code:
[rank_preimage_core.py](../experiments/rank_preimage_core.py),
[rank_preimage.py](../experiments/rank_preimage.py),
[rank_frontier_oracle.py](../experiments/rank_frontier_oracle.py).
Reproduce: `python3 experiments/check_rank_preimage.py` and
`python3 experiments/check_rank_closure_review.py`.

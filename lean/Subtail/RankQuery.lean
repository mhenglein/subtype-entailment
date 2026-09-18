import Subtail.RankMilestones

/-!
# Rank-query grammar, literal prefix-graph semantics, and the pinned Closure Lemma

This module PINS the statement of the promotion-preimage ("Closure") lemma of
the rank-query candidate (C080, stage 4a).  It proves NOTHING about that lemma.
Everything here is a definition, an executable decision procedure for the
finite query semantics with its correctness proof, or a `Prop` recording a
statement that later stages must prove.  No `sorry`, no custom axiom.

Conventions follow `experiments/rank_preimage_core.py` and the closure note
(`notes/2026-09-17-rank-query-closure-audit.md`, Section 1):

* a vertex colour is `(state, mask, next, root, end)`, with `next = none`
  standing for the compiler's `END` marker; no numeric position is a colour;
* edge labels are `F`, `S`, `K0`, `K1`, all DIRECTED; `S` is partial;
* an observer is a finite-state path automaton reading
  `(control, source colour, label, target colour) ↦ next controls`, with a
  per-control colour predicate `allows`;
* a clause has existential vertex variables, finite colour tests,
  equalities/disequalities between variables, and directed path atoms;
  a query is a finite union of clauses.  There are no inverse edges, no
  negated reachability, no path-label equality and no string variables.

The prefix graph of a labelled reference is defined LITERALLY from the word
(borders and longest matching prefixes), not through the stage-3 surgery
equations, so that the statement pinned here does not depend on any
construction that a proof may later use.
-/
namespace Subtail
namespace RankQuery
open TerminalRank RankMilestones

/-! ## Finite colours, labels, graphs, observers, queries -/

/-- Vertex colour: original cut state, incoming-flag mask over original states,
next reversed letter (`none` = END), root flag, end flag. -/
structure Colour (k : Nat) where
  state : Fin k
  mask : Vector Bool k
  next : Option Bool
  root : Bool
  isEnd : Bool
  deriving DecidableEq, Repr

/-- Directed edge labels: failure link, successor, KMP advance on a letter. -/
inductive Label where
  | F
  | S
  | K (a : Bool)
  deriving DecidableEq, Repr

def labels : List Label := [.F, .S, .K false, .K true]

theorem mem_labels (l : Label) : l ∈ labels := by
  cases l with
  | F => simp [labels]
  | S => simp [labels]
  | K a => cases a <;> simp [labels]

/-- A finite coloured graph with functional labelled edges; `S` may be absent. -/
structure Graph (k : Nat) where
  size : Nat
  colour : Fin size → Colour k
  edge : Fin size → Label → Option (Fin size)

/-- An epsilon-free finite-state path observer.  `allows` and `move` are
functions on the FINITE colour alphabet, i.e. finite tables. -/
structure Observer (k : Nat) where
  size : Nat
  initial : List (Fin size)
  final : List (Fin size)
  allows : Fin size → Colour k → Bool
  move : Fin size → Colour k → Label → Colour k → List (Fin size)

/-- A directed path atom `Path_O(source, target)` between clause variables. -/
structure Atom (k v : Nat) where
  observer : Observer k
  source : Fin v
  target : Fin v

/-- One conjunctive clause of the grammar. -/
structure Clause (k : Nat) where
  vars : Nat
  tests : List (Fin vars × (Colour k → Bool))
  equal : List (Fin vars × Fin vars)
  unequal : List (Fin vars × Fin vars)
  atoms : List (Atom k vars)

/-- A query is a finite union (disjunction) of clauses. -/
abbrev Query (k : Nat) := List (Clause k)

/-! ## Semantics: runs of an observer along a graph, satisfaction of a query -/

/-- A product node: graph vertex together with an observer control. -/
abbrev Node (G : Graph k) (O : Observer k) := Fin G.size × Fin O.size

def Allowed (G : Graph k) (O : Observer k) (x : Node G O) : Prop :=
  O.allows x.2 (G.colour x.1) = true

/-- One directed labelled step of the observer along a graph edge. -/
def Step (G : Graph k) (O : Observer k) (x y : Node G O) : Prop :=
  ∃ l : Label, G.edge x.1 l = some y.1 ∧
    y.2 ∈ O.move x.2 (G.colour x.1) l (G.colour y.1) ∧ Allowed G O y

/-- Directed runs; every visited node satisfies the observer's colour predicate. -/
inductive Run (G : Graph k) (O : Observer k) (x : Node G O) : Node G O → Prop
  | refl (h : Allowed G O x) : Run G O x x
  | step {y z : Node G O} (hy : Run G O x y) (hs : Step G O y z) : Run G O x z

/-- `Path_O(u, v)`: some directed path from `u` to `v` is accepted by `O`. -/
def Accepts (G : Graph k) (O : Observer k) (u v : Fin G.size) : Prop :=
  ∃ q ∈ O.initial, ∃ p ∈ O.final, Run G O (u, q) (v, p)

/-- Satisfaction of one clause under an existential vertex assignment. -/
def SatClause (G : Graph k) (c : Clause k) : Prop :=
  ∃ σ : Fin c.vars → Fin G.size,
    (∀ t ∈ c.tests, t.2 (G.colour (σ t.1)) = true) ∧
    (∀ e ∈ c.equal, σ e.1 = σ e.2) ∧
    (∀ e ∈ c.unequal, σ e.1 ≠ σ e.2) ∧
    ∀ a ∈ c.atoms, Accepts G a.observer (σ a.source) (σ a.target)

/-- `G ⊨ φ`: some clause of the union is satisfied. -/
def Sat (G : Graph k) (φ : Query k) : Prop := ∃ c ∈ φ, SatClause G c

/-! ## Weights (closure note, Section 3 and Section 5) -/

def sumSizes (c : Clause k) : Nat := (c.atoms.map fun a => a.observer.size).sum

/-- `T = max(2, 1 + v + a + Σ s_i)`. -/
def clauseWeight (c : Clause k) : Nat :=
  max 2 (1 + c.vars + c.atoms.length + sumSizes c)

def weight (φ : Query k) : Nat := maxNat (φ.map clauseWeight)

/-- `U_k(T) = 64 k T^(2T+2)`. -/
def closureBound (k T : Nat) : Nat := 64 * k * T ^ (2 * T + 2)

/-! ## Executable decision of `Sat` on a finite graph, with correctness proof -/

section Decision
variable (G : Graph k) (O : Observer k)

/-- All allowed successors of a product node, one list per edge label. -/
def succ (x : Node G O) : List (Node G O) :=
  labels.flatMap fun l =>
    match G.edge x.1 l with
    | none => []
    | some w =>
      ((O.move x.2 (G.colour x.1) l (G.colour w)).filter
        fun p => O.allows p (G.colour w)).map fun p => (w, p)

theorem mem_succ {x y : Node G O} : y ∈ succ G O x ↔ Step G O x y := by
  constructor
  · intro h
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp h
    refine ⟨l, ?_⟩
    revert hl
    cases he : G.edge x.1 l with
    | none => intro h; simp at h
    | some w =>
      intro h
      obtain ⟨p, hp, hpy⟩ := List.mem_map.mp h
      obtain ⟨hmove, hallow⟩ := List.mem_filter.mp hp
      subst hpy
      exact ⟨rfl, hmove, hallow⟩
  · rintro ⟨l, he, hmove, hallow⟩
    apply List.mem_flatMap.mpr
    refine ⟨l, mem_labels l, ?_⟩
    rw [he]
    apply List.mem_map.mpr
    exact ⟨y.2, List.mem_filter.mpr ⟨hmove, hallow⟩, rfl⟩

/-- Prepend every element of `s` that is not already present. -/
def addNew (v : List (Node G O)) : List (Node G O) → List (Node G O)
  | [] => v
  | y :: ys => addNew (if y ∈ v then v else y :: v) ys

/-- One saturation round. -/
def close (v : List (Node G O)) : List (Node G O) := addNew G O v (v.flatMap (succ G O))

def iter : Nat → List (Node G O) → List (Node G O)
  | 0, v => v
  | n + 1, v => iter n (close G O v)

/-- Every product node; only its length is used, as the saturation fuel. -/
def allNodes : List (Node G O) :=
  (List.finRange G.size).flatMap fun v => (List.finRange O.size).map fun q => (v, q)

theorem mem_allNodes (x : Node G O) : x ∈ allNodes G O := by
  apply List.mem_flatMap.mpr
  refine ⟨x.1, List.mem_finRange _, ?_⟩
  exact List.mem_map.mpr ⟨x.2, List.mem_finRange _, rfl⟩

/-- Nodes reachable from `x` after saturation; exact by the theorems below. -/
def reachable (x : Node G O) : List (Node G O) := iter G O (allNodes G O).length [x]

def acceptsCheck (u v : Fin G.size) : Bool :=
  O.initial.any fun q => O.allows q (G.colour u) &&
    O.final.any fun p => decide ((v, p) ∈ reachable G O (u, q))

theorem mem_addNew {v s : List (Node G O)} {y : Node G O} :
    y ∈ addNew G O v s ↔ y ∈ v ∨ y ∈ s := by
  induction s generalizing v with
  | nil => simp [addNew]
  | cons z zs ih =>
    simp only [addNew]
    rw [ih]
    by_cases hz : z ∈ v
    · simp only [hz, if_true, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hz)
        · exact Or.inr h
    · simp only [hz, if_false, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h

theorem nodup_addNew {v s : List (Node G O)} (hv : v.Nodup) : (addNew G O v s).Nodup := by
  induction s generalizing v with
  | nil => simpa [addNew] using hv
  | cons z zs ih =>
    simp only [addNew]
    by_cases hz : z ∈ v
    · simpa only [hz, if_true] using ih hv
    · simp only [hz, if_false]
      exact ih (List.nodup_cons.mpr ⟨hz, hv⟩)

theorem length_addNew_le {v s : List (Node G O)} : v.length ≤ (addNew G O v s).length := by
  induction s generalizing v with
  | nil => simp [addNew]
  | cons z zs ih =>
    simp only [addNew]
    by_cases hz : z ∈ v
    · simpa only [hz, if_true] using ih
    · simp only [hz, if_false]
      have h := ih (v := z :: v)
      simp only [List.length_cons] at h
      omega

/-- If a saturation round adds nothing, every offered node was already present. -/
theorem addNew_eq_subset {v s : List (Node G O)} (h : addNew G O v s = v) :
    ∀ y ∈ s, y ∈ v := by
  induction s generalizing v with
  | nil => simp
  | cons z zs ih =>
    intro y hy
    simp only [addNew] at h
    by_cases hz : z ∈ v
    · simp only [hz, if_true] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hz
      · exact ih h y hy
    · exfalso
      simp only [hz, if_false] at h
      have hl := congrArg List.length h
      have hle := length_addNew_le G O (v := z :: v) (s := zs)
      simp only [List.length_cons] at hle hl
      omega

theorem addNew_ne_lt {v s : List (Node G O)} (h : addNew G O v s ≠ v) :
    v.length < (addNew G O v s).length := by
  induction s generalizing v with
  | nil => exact absurd rfl h
  | cons z zs ih =>
    simp only [addNew] at h ⊢
    by_cases hz : z ∈ v
    · simp only [hz, if_true] at h ⊢
      exact ih h
    · simp only [hz, if_false] at h ⊢
      have hle := length_addNew_le G O (v := z :: v) (s := zs)
      simp only [List.length_cons] at hle
      omega

/-- Every node of a saturation is a genuine run from the seed. -/
theorem run_of_mem_iter {x : Node G O} :
    ∀ (n : Nat) (v : List (Node G O)), (∀ z ∈ v, Run G O x z) →
      ∀ y ∈ iter G O n v, Run G O x y := by
  intro n
  induction n with
  | zero => intro v hv y hy; exact hv y hy
  | succ n ih =>
    intro v hv y hy
    apply ih (close G O v) _ y hy
    intro z hz
    rcases (mem_addNew G O).mp hz with hz | hz
    · exact hv z hz
    · obtain ⟨w, hw, hzw⟩ := List.mem_flatMap.mp hz
      exact Run.step (hv w hw) ((mem_succ G O).mp hzw)

theorem subset_close {v : List (Node G O)} : ∀ y ∈ v, y ∈ close G O v := by
  intro y hy
  exact (mem_addNew G O).mpr (Or.inl hy)

theorem subset_iter {v : List (Node G O)} : ∀ n, ∀ y ∈ v, y ∈ iter G O n v := by
  intro n
  induction n generalizing v with
  | zero => intro y hy; exact hy
  | succ n ih => intro y hy; exact ih y (subset_close G O y hy)

theorem nodup_iter {v : List (Node G O)} (hv : v.Nodup) : ∀ n, (iter G O n v).Nodup := by
  intro n
  induction n generalizing v with
  | zero => exact hv
  | succ n ih => exact ih (nodup_addNew G O hv)

/-- Closed under successors: the invariant that makes saturation complete. -/
def IsClosed (v : List (Node G O)) : Prop := ∀ z ∈ v, ∀ y, Step G O z y → y ∈ v

theorem isClosed_of_fixed {v : List (Node G O)} (h : close G O v = v) : IsClosed G O v := by
  intro z hz y hs
  apply addNew_eq_subset G O h
  exact List.mem_flatMap.mpr ⟨z, hz, (mem_succ G O).mpr hs⟩

theorem iter_of_fixed {v : List (Node G O)} (h : close G O v = v) : ∀ n, iter G O n v = v := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, h, ih]

/-- Either saturation has already closed, or it has grown by one node per round. -/
theorem closed_or_grow {v : List (Node G O)} :
    ∀ n, IsClosed G O (iter G O n v) ∨ v.length + n ≤ (iter G O n v).length := by
  intro n
  induction n generalizing v with
  | zero => exact Or.inr (by simp [iter])
  | succ n ih =>
    by_cases hf : close G O v = v
    · left
      rw [iter, hf, iter_of_fixed G O hf]
      exact isClosed_of_fixed G O hf
    · rcases ih (v := close G O v) with hc | hl
      · exact Or.inl hc
      · right
        have hlt := addNew_ne_lt G O hf
        simp only [iter]
        change v.length + (n + 1) ≤ (iter G O n (close G O v)).length
        change v.length < (close G O v).length at hlt
        omega

theorem isClosed_reachable (x : Node G O) : IsClosed G O (reachable G O x) := by
  rcases closed_or_grow G O (v := [x]) (allNodes G O).length with hc | hl
  · exact hc
  · exfalso
    have hn := nodup_iter G O (v := [x]) (by simp) (allNodes G O).length
    have hle := hn.length_le_of_subset (l₂ := allNodes G O) (fun y _ => mem_allNodes G O y)
    simp only [List.length_singleton] at hl
    omega

theorem mem_of_run_closed {S : List (Node G O)} (hS : IsClosed G O S) {x y : Node G O}
    (hx : x ∈ S) (hr : Run G O x y) : y ∈ S := by
  induction hr with
  | refl _ => exact hx
  | step _ hs ih => exact hS _ ih _ hs

theorem allowed_of_run {x y : Node G O} (hr : Run G O x y) : Allowed G O x := by
  induction hr with
  | refl h => exact h
  | step _ _ ih => exact ih

theorem mem_reachable_iff {x y : Node G O} (hx : Allowed G O x) :
    y ∈ reachable G O x ↔ Run G O x y := by
  constructor
  · intro hy
    refine run_of_mem_iter G O _ [x] ?_ y hy
    intro z hz
    simp only [List.mem_singleton] at hz
    subst hz
    exact Run.refl hx
  · intro hr
    exact mem_of_run_closed G O (isClosed_reachable G O x)
      (subset_iter G O _ x (by simp)) hr

theorem acceptsCheck_correct (u v : Fin G.size) :
    acceptsCheck G O u v = true ↔ Accepts G O u v := by
  simp only [acceptsCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Accepts]
  constructor
  · rintro ⟨q, hq, hallow, p, hp, hmem⟩
    have hallow' : Allowed G O (u, q) := hallow
    exact ⟨q, hq, p, hp, (mem_reachable_iff G O (x := (u, q)) hallow').mp hmem⟩
  · rintro ⟨q, hq, p, hp, hr⟩
    have hallow : Allowed G O (u, q) := allowed_of_run G O hr
    exact ⟨q, hq, hallow, p, hp, (mem_reachable_iff G O (x := (u, q)) hallow).mpr hr⟩

end Decision

/-- All lists of a given length over `Fin n`. -/
def allLists (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | v + 1 => (List.finRange n).flatMap fun x => (allLists n v).map fun l => x :: l

theorem mem_allLists {n : Nat} : ∀ {v : Nat} (l : List (Fin n)), l.length = v → l ∈ allLists n v := by
  intro v
  induction v with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero hl
    simp [this, allLists]
  | succ v ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons x t =>
      simp only [List.length_cons] at hl
      simp only [allLists]
      apply List.mem_flatMap.mpr
      exact ⟨x, List.mem_finRange x, List.mem_map.mpr ⟨t, ih t (by omega), rfl⟩⟩

/-- Read a list of length `v` as an assignment `Fin v → Fin n`. -/
def toFun {n v : Nat} (l : List (Fin n)) (h : l.length = v) : Fin v → Fin n :=
  fun i => l[i.val]'(by rw [h]; exact i.isLt)

theorem toFun_ofFn {n v : Nat} (σ : Fin v → Fin n) :
    toFun (List.ofFn σ) List.length_ofFn = σ := by
  funext i
  simp [toFun]

def clauseCheckWith (G : Graph k) (c : Clause k) (σ : Fin c.vars → Fin G.size) : Bool :=
  c.tests.all (fun t => t.2 (G.colour (σ t.1))) &&
  c.equal.all (fun e => decide (σ e.1 = σ e.2)) &&
  c.unequal.all (fun e => decide (σ e.1 ≠ σ e.2)) &&
  c.atoms.all (fun a => acceptsCheck G a.observer (σ a.source) (σ a.target))

def clauseCheck (G : Graph k) (c : Clause k) : Bool :=
  (allLists G.size c.vars).any fun l =>
    if h : l.length = c.vars then clauseCheckWith G c (toFun l h) else false

/-- Executable satisfaction test for a finite union of clauses. -/
def satCheck (G : Graph k) (φ : Query k) : Bool := φ.any (clauseCheck G)

theorem clauseCheckWith_correct (G : Graph k) (c : Clause k) (σ : Fin c.vars → Fin G.size) :
    clauseCheckWith G c σ = true ↔
      (∀ t ∈ c.tests, t.2 (G.colour (σ t.1)) = true) ∧
      (∀ e ∈ c.equal, σ e.1 = σ e.2) ∧
      (∀ e ∈ c.unequal, σ e.1 ≠ σ e.2) ∧
      ∀ a ∈ c.atoms, Accepts G a.observer (σ a.source) (σ a.target) := by
  simp only [clauseCheckWith, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun a ha => (acceptsCheck_correct G _ _ _).mp (h4 a ha)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun a ha => (acceptsCheck_correct G _ _ _).mpr (h4 a ha)⟩

theorem clauseCheck_correct (G : Graph k) (c : Clause k) :
    clauseCheck G c = true ↔ SatClause G c := by
  simp only [clauseCheck, List.any_eq_true]
  constructor
  · rintro ⟨l, -, hl⟩
    by_cases h : l.length = c.vars
    · simp only [h, dite_true] at hl
      exact ⟨toFun l h, (clauseCheckWith_correct G c _).mp hl⟩
    · simp [h] at hl
  · rintro ⟨σ, hσ⟩
    refine ⟨List.ofFn σ, mem_allLists _ List.length_ofFn, ?_⟩
    have hlen : (List.ofFn σ).length = c.vars := List.length_ofFn
    simp only [hlen, dite_true]
    rw [toFun_ofFn]
    exact (clauseCheckWith_correct G c σ).mpr hσ

theorem satCheck_correct (G : Graph k) (φ : Query k) : satCheck G φ = true ↔ Sat G φ := by
  simp only [satCheck, List.any_eq_true, Sat]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, (clauseCheck_correct G c).mp h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, (clauseCheck_correct G c).mpr h⟩

instance (G : Graph k) (φ : Query k) : Decidable (Sat G φ) :=
  decidable_of_iff _ (satCheck_correct G φ)

/-! ## Labelled references and their literal prefix graphs -/

/-- A reversed reference `rho = word` with original cut states `label 0 .. label m`;
`label 0` is the reversed word's start, i.e. the accepting end of the original run.
Values of `label` beyond `word.length` are irrelevant. -/
structure Reference (k : Nat) where
  word : Word
  label : Nat → Fin k

/-- Incoming-flag mask at cut `j`: original states `p` with `(p, r_b) ∈ G` for
some border `b` of `rho[:j]`, including the empty border `0` and the full border `j`. -/
def mask (I : Instance k) (B : Reference k) (j : Nat) : Vector Bool k :=
  Vector.ofFn fun p => (borderLengths (B.word.take j)).any fun h => (I.flags.get p).get (B.label h)

/-- Literal KMP advance: the longest prefix of `rho` (of length at most `|rho|`)
that is a suffix of `rho[:j] ++ [a]`.  At `j = |rho|` this is the full-pattern
fallback, since the length-`|rho|+1` candidate is excluded. -/
def advance (w : Word) (j : Nat) (a : Bool) : Nat :=
  maxNat ((List.range (w.length + 1)).filter fun h => (w.take h).isSuffixOf (w.take j ++ [a]))

theorem advance_le (w : Word) (j : Nat) (a : Bool) : advance w j a ≤ w.length := by
  have hz : 0 ∈ (List.range (w.length + 1)).filter
      (fun h => (w.take h).isSuffixOf (w.take j ++ [a])) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (Nat.succ_pos _), ?_⟩
    simp
  have hm := maxNat_mem hz
  have hr := (List.mem_filter.mp hm).1
  have := List.mem_range.mp hr
  simp only [advance]
  omega

theorem failureParent_take_le (w : Word) (j : Nat) : failureParent (w.take j) ≤ w.length := by
  by_cases hz : (w.take j).length = 0
  · have : w.take j = [] := List.eq_nil_of_length_eq_zero hz
    simp [this]
  · have hs := (failureParent_spec (w.take j) (by omega)).2.1
    have hl : (w.take j).length ≤ w.length := by
      simp only [List.length_take]
      exact Nat.min_le_right _ _
    omega

/-- The literal coloured prefix graph `P(B)` on vertices `0 .. |rho|`. -/
def prefixGraph (I : Instance k) (B : Reference k) : Graph k where
  size := B.word.length + 1
  colour := fun j =>
    ⟨B.label j.val, mask I B j.val, B.word[j.val]?,
      decide (j.val = 0), decide (j.val = B.word.length)⟩
  edge := fun j l =>
    match l with
    | .F => some ⟨failureParent (B.word.take j.val),
        Nat.lt_succ_of_le (failureParent_take_le _ _)⟩
    | .S => if h : j.val < B.word.length then some ⟨j.val + 1, by omega⟩ else none
    | .K a => some ⟨advance B.word j.val a, Nat.lt_succ_of_le (advance_le _ _ _)⟩

/-- A safe labelled reference: nonempty, starts at an accepting state, follows the
automaton in reverse, avoids `Bad`, and passes every border-chain flag test
(including diagonal pairs and the empty border). -/
structure SafeReference (I : Instance k) (B : Reference k) : Prop where
  nonempty : 0 < B.word.length
  accepting : I.final.get (B.label 0) = true
  run : ∀ j, (hj : j < B.word.length) →
    step I (B.label (j + 1)) (B.word[j]'hj) = some (B.label j)
  safe : ∀ j, j ≤ B.word.length → I.bad.get (B.label j) = false
  border : ∀ j, j ≤ B.word.length → (mask I B j).get (B.label j) = false

/-- `C` is a safe FIRST-RETURN extension of `B`: it extends the word and the labels,
and the old word reoccurs exactly once more, ending at the new endpoint
(`FirstReturn` from `RankMilestones`; overlapping returns and `L = 1` included). -/
structure FirstReturnExt (I : Instance k) (B C : Reference k) : Prop where
  safe : SafeReference I C
  word : B.word <+: C.word
  label : ∀ j, j ≤ B.word.length → C.label j = B.label j
  firstReturn : FirstReturn C.word B.word.length C.word.length

/-! ## The pinned Closure Lemma (stage 4) -/

/-- `pre` is a correct promotion preimage for `I`: for every query and every safe
reference, `P(B) ⊨ pre φ` iff some safe first-return extension `C` has `P(C) ⊨ φ`,
and each clause of `pre φ` has weight at most `U_k(weight φ)`. -/
def ClosureFor (I : Instance k) (pre : Query k → Query k) : Prop :=
  (∀ (φ : Query k) (B : Reference k), SafeReference I B →
    (Sat (prefixGraph I B) (pre φ) ↔
      ∃ C : Reference k, FirstReturnExt I B C ∧ Sat (prefixGraph I C) φ)) ∧
  ∀ φ : Query k, ∀ c ∈ pre φ, clauseWeight c ≤ closureBound k (weight φ)

/-- **Closure Lemma (C080, stage 4), as a statement.**  For a terminal instance,
some promotion preimage exists.  Unproved here; referee brief Section 3. -/
def ClosureStatement (I : Instance k) : Prop :=
  TerminalFinals I → ∃ pre : Query k → Query k, ClosureFor I pre

/-! ## The finishing query and the decision schema that would follow -/

/-- One directed edge with the given label; two controls. -/
def oneEdge (l : Label) : Observer k where
  size := 2
  initial := [⟨0, by omega⟩]
  final := [⟨1, by omega⟩]
  allows := fun _ _ => true
  move := fun q _ l' _ => if q.val = 0 ∧ l' = l then [⟨1, by omega⟩] else []

/-- The finishing observer: carries the actual original state, forbids the graph
endpoint, and on `K_a` moves to a predecessor `p` that is safe, non-diagonal and
outside the target's mask; accepts at the original initial state. -/
def finishObserver (I : Instance k) (q : Fin k) : Observer k where
  size := k
  initial := [q]
  final := [I.initial]
  allows := fun _ c => !c.isEnd
  move := fun q _ l d =>
    match l with
    | .K a => if d.isEnd then [] else
        (List.finRange k).filter fun p =>
          step I p a == some q && !I.bad.get p && !(I.flags.get p).get p && !d.mask.get p
    | _ => []

/-- `Finish_I`: variables `e, f, x`; `e` is the endpoint with state `q`; one `F`
edge `e → f`; a finishing path `f → x` ending at the initial state. One clause
per original state `q`. -/
def finishQuery (I : Instance k) : Query k :=
  (List.finRange k).map fun q =>
    { vars := 3
      tests := [(⟨0, by omega⟩, fun c => c.isEnd && decide (c.state = q))]
      equal := []
      unequal := []
      atoms := [⟨oneEdge .F, ⟨0, by omega⟩, ⟨1, by omega⟩⟩,
                ⟨finishObserver I q, ⟨1, by omega⟩, ⟨2, by omega⟩⟩] }

/-- `Φ_0 = Finish`, `Φ_(h+1) = Φ_h ∨ pre Φ_h`. -/
def promote (pre : Query k → Query k) (φ : Query k) : Nat → Query k
  | 0 => φ
  | h + 1 => promote pre φ h ++ pre (promote pre φ h)

/-- The one-letter reference `a` with reversed cut states `f` (accepting end) and `p`. -/
def oneLetter (a : Bool) (f p : Fin k) : Reference k where
  word := [a]
  label := fun j => if j = 0 then f else p

/-- **Decision schema (stages 4-5 target).**  Given a closure map, a nonempty
witness exists iff some safe one-letter reference satisfies `Φ_(k-2)`.  Stated
against the repository's original `Witness` predicate.  Unproved here. -/
def RankDecisionStatement (I : Instance k) (pre : Query k → Query k) : Prop :=
  ((∃ w : Word, Witness I w) ↔
    Witness I [] ∨ ∃ (a : Bool) (f p : Fin k),
      SafeReference I (oneLetter a f p) ∧
      Sat (prefixGraph I (oneLetter a f p)) (promote pre (finishQuery I) (k - 2)))

/-! ## Executable sanity checks on a one-state instance (compiler toy fixtures) -/

/-- The one-state toy instance of `check_rank_preimage.py`: both letters loop, no flags. -/
def toy : Instance 1 where
  initial := ⟨0, by omega⟩
  transitions := #v[(some ⟨0, by omega⟩, some ⟨0, by omega⟩)]
  bad := #v[false]
  final := #v[true]
  flags := #v[#v[false]]

def toyRef (w : Word) : Reference 1 := ⟨w, fun _ => ⟨0, by omega⟩⟩

/-- Observer with one control that reads only the given labels. -/
def loopObserver (ls : List Label) : Observer k where
  size := 1
  initial := [⟨0, by omega⟩]
  final := [⟨0, by omega⟩]
  allows := fun _ _ => true
  move := fun _ _ l _ => if l ∈ ls then [⟨0, by omega⟩] else []

/-- `x` is the endpoint, `y` is the root, and one path atom `x → y`. -/
def endToRoot (O : Observer k) : Query k :=
  [{ vars := 2
     tests := [(⟨0, by omega⟩, fun c => c.isEnd), (⟨1, by omega⟩, fun c => c.root)]
     equal := []
     unequal := []
     atoms := [⟨O, ⟨0, by omega⟩, ⟨1, by omega⟩⟩] }]

-- P("0"): F reaches the root from the endpoint; S cannot leave the endpoint;
-- K0 from the endpoint of "0" returns to 1, never to the root; K1 falls to 0.
#guard satCheck (prefixGraph toy (toyRef [false])) (endToRoot (loopObserver [.F])) = true
#guard satCheck (prefixGraph toy (toyRef [false])) (endToRoot (loopObserver [.S])) = false
#guard satCheck (prefixGraph toy (toyRef [false])) (endToRoot (loopObserver [.K false])) = false
#guard satCheck (prefixGraph toy (toyRef [false])) (endToRoot (loopObserver [.K true])) = true
-- The literal graph of "010": F(3)=1, K0(3)=1, K1(3)=2; S is absent at the endpoint.
#guard (prefixGraph toy (toyRef [false, true, false])).edge ⟨3, by decide⟩ .F = some ⟨1, by decide⟩
#guard (prefixGraph toy (toyRef [false, true, false])).edge ⟨3, by decide⟩ (.K false) = some ⟨1, by decide⟩
#guard (prefixGraph toy (toyRef [false, true, false])).edge ⟨3, by decide⟩ (.K true) = some ⟨2, by decide⟩
#guard (prefixGraph toy (toyRef [false, true, false])).edge ⟨3, by decide⟩ .S = none
#guard (prefixGraph toy (toyRef [false, true, false])).edge ⟨2, by decide⟩ (.K false) = some ⟨3, by decide⟩
-- Finishing from "0" on the toy: the reversed run may stop at once (empty finishing walk).
#guard satCheck (prefixGraph toy (toyRef [false])) (finishQuery toy) = true
#guard (finishQuery toy).map clauseWeight = [9]

end RankQuery
end Subtail

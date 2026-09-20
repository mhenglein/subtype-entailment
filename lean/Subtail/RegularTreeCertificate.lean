import Subtail.ExpressionNormalization

/-!
# Finite regular-tree countermodel certificates

This module verifies a supplied finite graph certificate for a negative
expression-entailment instance.  A graph node is either bottom (`none`) or a
binary product (`some (left,right)`).  Graph unfolding may be cyclic, so it
denotes an arbitrary, possibly infinite regular tree.

The checker does not extract a graph.  It checks a finite simulation relation
supplied with the graph, expression-to-node embeddings for the finite input
forest, all premise pairs, and one supplied separating word.  The relation is
enough to prove arbitrary-tree inclusion, while the word check proves query
failure.  The extraction and completeness of a Python producer remain outside
this module.
-/

namespace Subtail
namespace RegularTreeCertificate

open TreeSemantics ExpressionNormalization

/-! ## Finite graphs and their arbitrary-tree unfoldings -/

/-- `none` is a bottom node; `some (left,right)` is a binary product node. -/
abbrev Node (v : Nat) := Option (Fin v × Fin v)

/-- A finite directed graph whose product edges point to graph nodes. -/
structure Graph (v : Nat) where
  nodes : Vector (Node v) v

/-- Membership of a finite word in the tree rooted at a graph node. -/
def graphNodes (G : Graph v) (i : Fin v) : Word → Bool
  | [] => match G.nodes.get i with
    | none => false
    | some _ => true
  | b :: w => match G.nodes.get i with
    | none => false
    | some (left, right) => graphNodes G (if b then right else left) w

theorem graphNodes_prefix (G : Graph v) (i : Fin v) {u w : Word}
    (h : graphNodes G i (u ++ w) = true) : graphNodes G i u = true := by
  induction u generalizing i with
  | nil =>
      have h' : graphNodes G i w = true := by simpa using h
      induction w generalizing i with
      | nil => exact h'
      | cons b w ihw =>
          cases hn : G.nodes.get i with
          | none => simp [graphNodes, hn] at h'
          | some pair => simp [graphNodes, hn]
  | cons b u ih =>
      cases hn : G.nodes.get i with
      | none => simp [graphNodes, hn] at h
      | some pair =>
          have h' : graphNodes G (if b then pair.2 else pair.1) (u ++ w) = true := by
            simpa [graphNodes, hn] using h
          have hu := ih (i := if b then pair.2 else pair.1) h'
          simpa [graphNodes, hn] using hu

/-- The regular tree obtained by unfolding a graph node. -/
def treeOf (G : Graph v) (i : Fin v) : Tree where
  nodes := fun w => graphNodes G i w = true
  closed := by
    intro u w h
    exact graphNodes_prefix G i h

theorem tree_eq_of_nodes {X Y : Tree} (h : ∀ w, X.nodes w ↔ Y.nodes w) : X = Y := by
  cases X with
  | mk xn xc =>
      cases Y with
      | mk yn yc =>
          have he : xn = yn := funext fun w => propext (h w)
          cases he
          rfl

theorem treeOf_product (G : Graph v) (i left right : Fin v)
    (h : G.nodes.get i = some (left, right)) :
    treeOf G i = product (treeOf G left) (treeOf G right) := by
  apply tree_eq_of_nodes
  intro w
  cases w with
  | nil => simp [treeOf, graphNodes, h]
  | cons b w =>
      cases b <;> simp [treeOf, graphNodes, h]

/-! ## Finite simulation certificates for graph inclusion -/

/-- One local simulation obligation for a Boolean relation. -/
def simulationStep (G : Graph v) (R : Fin v → Fin v → Bool)
    (i j : Fin v) : Bool :=
  match G.nodes.get i, G.nodes.get j with
  | none, _ => true
  | some _, none => false
  | some (i₀, i₁), some (j₀, j₁) => R i₀ j₀ && R i₁ j₁

/-- Check local closure of every true pair in a finite relation table. -/
def simulationCheck (G : Graph v) (R : Fin v → Fin v → Bool) : Bool :=
  (List.finRange v).all fun i =>
    (List.finRange v).all fun j => !R i j || simulationStep G R i j

theorem simulationCheck_closed (G : Graph v) (R : Fin v → Fin v → Bool)
    (h : simulationCheck G R = true) {i j : Fin v} (hr : R i j = true) :
    simulationStep G R i j = true := by
  have hi := (List.all_eq_true.mp h) i (List.mem_finRange i)
  have hij := (List.all_eq_true.mp hi) j (List.mem_finRange j)
  simp [hr] at hij
  exact hij

theorem simulation_sound (G : Graph v) (R : Fin v → Fin v → Bool)
    (hclosed : ∀ i j, R i j = true → simulationStep G R i j = true)
    {i j : Fin v} (hr : R i j = true) :
    Below (treeOf G i) (treeOf G j) := by
  intro w hw
  induction w generalizing i j with
  | nil =>
      cases hi : G.nodes.get i with
      | none => simp [treeOf, graphNodes, hi] at *
      | some pair =>
          cases hj : G.nodes.get j with
          | none =>
              have hs := hclosed i j hr
              simp [simulationStep, hi, hj] at hs
          | some _ => simp [treeOf, graphNodes, hj]
  | cons b w ih =>
      cases hi : G.nodes.get i with
      | none => simp [treeOf, graphNodes, hi] at *
      | some pair =>
          cases hj : G.nodes.get j with
          | none =>
              have hs := hclosed i j hr
              simp [simulationStep, hi, hj] at hs
          | some target =>
              have hs := hclosed i j hr
              simp only [simulationStep, hi, hj, Bool.and_eq_true] at hs
              cases b with
              | false =>
                  have hsource : graphNodes G pair.1 w = true := by
                    simpa [treeOf, graphNodes, hi] using hw
                  have hchild := ih (i := pair.1) (j := target.1) hs.1 hsource
                  simpa [treeOf, graphNodes, hj] using hchild
              | true =>
                  have hsource : graphNodes G pair.2 w = true := by
                    simpa [treeOf, graphNodes, hi] using hw
                  have hchild := ih (i := pair.2) (j := target.2) hs.2 hsource
                  simpa [treeOf, graphNodes, hj] using hchild

/-- A proposition-valued simulation relation on a finite graph. -/
def SimulationStep (G : Graph v) (R : Fin v → Fin v → Prop)
    (i j : Fin v) : Prop :=
  match G.nodes.get i, G.nodes.get j with
  | none, _ => True
  | some _, none => False
  | some (i₀, i₁), some (j₀, j₁) => R i₀ j₀ ∧ R i₁ j₁

def IsSimulation (G : Graph v) (R : Fin v → Fin v → Prop) : Prop :=
  ∀ i j, R i j → SimulationStep G R i j

theorem simulation_sound_prop (G : Graph v) (R : Fin v → Fin v → Prop)
    (hclosed : IsSimulation G R) {i j : Fin v} (hr : R i j) :
    Below (treeOf G i) (treeOf G j) := by
  intro w hw
  induction w generalizing i j with
  | nil =>
      cases hi : G.nodes.get i with
      | none => simp [treeOf, graphNodes, hi] at *
      | some pair =>
          cases hj : G.nodes.get j with
          | none =>
              have hs := hclosed i j hr
              simp [SimulationStep, hi, hj] at hs
          | some _ => simp [treeOf, graphNodes, hj]
  | cons b w ih =>
      cases hi : G.nodes.get i with
      | none => simp [treeOf, graphNodes, hi] at *
      | some pair =>
          cases hj : G.nodes.get j with
          | none =>
              have hs := hclosed i j hr
              simp [SimulationStep, hi, hj] at hs
          | some target =>
              have hs := hclosed i j hr
              cases b with
              | false =>
                  have hs' : R pair.1 target.1 := by
                    have hsp : R pair.1 target.1 ∧ R pair.2 target.2 := by
                      simpa [SimulationStep, hi, hj] using hs
                    exact hsp.1
                  have hsource : graphNodes G pair.1 w = true := by
                    simpa [treeOf, graphNodes, hi] using hw
                  have hchild := ih (i := pair.1) (j := target.1) hs' hsource
                  simpa [treeOf, graphNodes, hj] using hchild
              | true =>
                  have hs' : R pair.2 target.2 := by
                    have hsp : R pair.1 target.1 ∧ R pair.2 target.2 := by
                      simpa [SimulationStep, hi, hj] using hs
                    exact hsp.2
                  have hsource : graphNodes G pair.2 w = true := by
                    simpa [treeOf, graphNodes, hi] using hw
                  have hchild := ih (i := pair.2) (j := target.2) hs' hsource
                  simpa [treeOf, graphNodes, hj] using hchild

/-- Graph inclusion is exactly the existence of a finite locally closed simulation.

The forward relation is semantic and is used only in this theorem; executable
certificates supply a Boolean table and are checked by `simulationCheck`.
-/
theorem below_iff_simulation (G : Graph v) (i j : Fin v) :
    Below (treeOf G i) (treeOf G j) ↔
      ∃ R : Fin v → Fin v → Prop, R i j ∧ IsSimulation G R := by
  constructor
  · intro h
    let R : Fin v → Fin v → Prop := fun p q => Below (treeOf G p) (treeOf G q)
    refine ⟨R, h, ?_⟩
    intro p q hpq
    cases hp : G.nodes.get p with
    | none => simpa [SimulationStep, hp]
    | some pchildren =>
        cases hq : G.nodes.get q with
        | none =>
            have hroot := hpq []
            simp [R, treeOf, graphNodes, hp, hq] at hroot
        | some qchildren =>
            simp only [SimulationStep, hp, hq]
            constructor
            · intro w hw
              simpa [R, treeOf, graphNodes, hq] using
                (hpq (false :: w) (by simpa [R, treeOf, graphNodes, hp] using hw))
            · intro w hw
              simpa [R, treeOf, graphNodes, hq] using
                (hpq (true :: w) (by simpa [R, treeOf, graphNodes, hp] using hw))
  · rintro ⟨R, hij, hclosed⟩
    exact simulation_sound_prop G R hclosed hij

/-! ## Certificates and expression embeddings -/

structure Certificate (n v : Nat) where
  graph : Graph v
  roots : Fin n → Fin v
  embed : Expr n → Fin v
  relation : Fin v → Fin v → Bool
  word : Word

def valuation (c : Certificate n v) : Valuation n :=
  fun x => treeOf c.graph (c.roots x)

/-- Check that the finite expression forest is represented by graph nodes. -/
def embedCheck (c : Certificate n v) : Expr n → Bool
  | .var x => decide (c.embed (.var x) = c.roots x)
  | .bot => match c.graph.nodes.get (c.embed .bot) with
    | none => true
    | some _ => false
  | .prod l r =>
      match c.graph.nodes.get (c.embed (.prod l r)) with
      | none => false
      | some (left, right) =>
          decide (left = c.embed l) && decide (right = c.embed r) &&
            embedCheck c l && embedCheck c r

def expressionForest (G : Input n) (s t : Expr n) : List (Expr n) :=
  s :: t :: G.flatMap (fun c => [c.1, c.2])

theorem embed_eval (c : Certificate n v) (e : Expr n)
    (h : embedCheck c e = true) :
    treeOf c.graph (c.embed e) = eval (valuation c) e := by
  induction e with
  | var x =>
      have he : c.embed (.var x) = c.roots x := by
        simpa [embedCheck] using h
      simpa [eval, valuation] using congrArg (fun z => treeOf c.graph z) he
  | bot =>
      have hn : c.graph.nodes.get (c.embed .bot) = none := by
        cases hh : c.graph.nodes.get (c.embed .bot) with
        | none => rfl
        | some pair => simp [embedCheck, hh] at h
      apply tree_eq_of_nodes
      intro w
      cases w with
      | nil => simp [treeOf, graphNodes, hn, eval, valuation, bottom]
      | cons b w => simp [treeOf, graphNodes, hn, eval, valuation, bottom]
  | prod l r ihl ihr =>
      cases hn : c.graph.nodes.get (c.embed (.prod l r)) with
      | none => simp [embedCheck, hn] at h
      | some pair =>
          have hparts :
              pair.1 = c.embed l ∧ pair.2 = c.embed r ∧
                embedCheck c l = true ∧ embedCheck c r = true := by
            simpa [embedCheck, hn, Bool.and_eq_true, decide_eq_true_eq,
              and_assoc] using h
          have hl : pair.1 = c.embed l := hparts.1
          have hr : pair.2 = c.embed r := hparts.2.1
          have hleft : embedCheck c l = true := hparts.2.2.1
          have hright : embedCheck c r = true := hparts.2.2.2
          rw [treeOf_product c.graph _ _ _ hn, hl, hr]
          simp only [eval]
          rw [ihl hleft, ihr hright]

/-! ## Executable checker and semantic soundness -/

def premisesCheck (c : Certificate n v) (G : Input n) : Bool :=
  G.all fun p => c.relation (c.embed p.1) (c.embed p.2)

def check (G : Input n) (s t : Expr n) (c : Certificate n v) : Bool :=
  simulationCheck c.graph c.relation &&
    (expressionForest G s t).all (embedCheck c) &&
    premisesCheck c G &&
    graphNodes c.graph (c.embed s) c.word &&
    !(graphNodes c.graph (c.embed t) c.word)

theorem check_sound (G : Input n) (s t : Expr n) (c : Certificate n v)
    (h : check G s t c = true) :
    ExprModels G (valuation c) ∧
      (eval (valuation c) s).nodes c.word ∧
      ¬ (eval (valuation c) t).nodes c.word := by
  unfold check at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have h4 := Bool.and_eq_true_iff.mp h3.1
  have hclosed : simulationCheck c.graph c.relation = true := h4.1
  have hem : (expressionForest G s t).all (embedCheck c) = true := h4.2
  have hprem : premisesCheck c G = true := h3.2
  have hleft : graphNodes c.graph (c.embed s) c.word = true := h2.2
  have hright := h1.2
  have hclosed' : ∀ i j, c.relation i j = true →
      simulationStep c.graph c.relation i j = true := by
    intro i j hr
    exact simulationCheck_closed c.graph c.relation hclosed hr
  have heforest : ∀ e ∈ expressionForest G s t, embedCheck c e = true := by
    intro e he
    exact (List.all_eq_true.mp hem) e he
  have hmodel : ExprModels G (valuation c) := by
    intro p hp
    have hpRel : c.relation (c.embed p.1) (c.embed p.2) = true := by
      exact (List.all_eq_true.mp hprem) p hp
    have hbelow := simulation_sound c.graph c.relation hclosed' hpRel
    have hp1 : p.1 ∈ expressionForest G s t := by
      unfold expressionForest
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨p, hp, by simp⟩))
    have hp2 : p.2 ∈ expressionForest G s t := by
      unfold expressionForest
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨p, hp, by simp⟩))
    rw [embed_eval c p.1 (heforest _ hp1), embed_eval c p.2 (heforest _ hp2)] at hbelow
    exact hbelow
  have hs : embedCheck c s = true := heforest _ (by simp [expressionForest])
  have ht : embedCheck c t = true := heforest _ (by simp [expressionForest])
  have hse := embed_eval c s hs
  have hte := embed_eval c t ht
  refine ⟨hmodel, ?_, ?_⟩
  · rw [← hse]
    exact hleft
  · rw [← hte]
    have hfalse : graphNodes c.graph (c.embed t) c.word = false := by
      cases hv : graphNodes c.graph (c.embed t) c.word with
      | false => rfl
      | true => simp [hv] at hright
    intro ht
    have : graphNodes c.graph (c.embed t) c.word = true := ht
    cases hfalse.symm.trans this

theorem check_not_entails (G : Input n) (s t : Expr n) (c : Certificate n v)
    (h : check G s t c = true) : ¬ ExprEntails G s t := by
  intro hEntails
  obtain ⟨hm, hs, ht⟩ := check_sound G s t c h
  exact ht (hEntails (valuation c) hm c.word hs)

end RegularTreeCertificate
end Subtail

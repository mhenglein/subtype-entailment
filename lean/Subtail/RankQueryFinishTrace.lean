import Subtail.RankQueryFinishFacts
import Subtail.RankQuerySound

/-!
# Exact finishing-query trace semantics

Uses the EXISTING finishQuery, prefixGraph, observer run and original machine.
A trace records actual letters and reverse states. Every cursor stays strictly
below the reference endpoint. No compiler-closure, rank, witness bound, or
arbitrary-completion equivalence is assumed.
-/
namespace Subtail
namespace RankQueryFinishTrace
open TerminalRank RankMilestones RankQuery RankQueryFinishFacts

variable {k : Nat}

abbrev Pos (B : Reference k) := Fin (B.word.length + 1)

/-- The old endpoint, not a permitted finishing cursor. -/
def endpoint (B : Reference k) : Pos B := ⟨B.word.length, Nat.lt_succ_self _⟩

/-- Finishing starts at the failure parent, not at the full reference. -/
def parent (B : Reference k) : Pos B :=
  ⟨failureParent B.word, Nat.lt_succ_of_le (by
    simpa only [List.take_length] using failureParent_take_le B.word B.word.length)⟩

theorem end_edge (I : Instance k) (B : Reference k) :
    (prefixGraph I B).edge (endpoint B) .F = some (parent B) := by
  simp only [prefixGraph, endpoint, List.take_length, parent]

theorem notEnd_iff (I : Instance k) (B : Reference k) (v : Pos B) :
    ((prefixGraph I B).colour v).isEnd = false ↔ v.val < B.word.length := by
  change decide (v.val = B.word.length) = false ↔ v.val < B.word.length
  rw [decide_eq_false_iff_not]
  have hv := v.isLt
  omega

theorem k_edge_iff (I : Instance k) (B : Reference k) (u v : Pos B) (a : Bool) :
    (prefixGraph I B).edge u (.K a) = some v ↔
      RankQuery.advance B.word u.val a = v.val := by
  constructor
  · intro he
    exact congrArg Fin.val (Option.some.inj he)
  · intro he
    exact congrArg some (Fin.ext he)

theorem prefix_step_iff (I : Instance k) (B : Reference k) (q0 q p : Fin k)
    (u v : Pos B) :
    Step (prefixGraph I B) (finishObserver I q0) (u,q) (v,p) ↔
      ∃ a : Bool, RankQuery.advance B.word u.val a = v.val ∧
        v.val < B.word.length ∧ step I p a = some q ∧
        I.bad.get p = false ∧ (I.flags.get p).get p = false ∧
        (mask I B v.val).get p = false := by
  rw [finish_step_iff]
  constructor
  · rintro ⟨a, he, hn, hs, hb, hd, hm⟩
    exact ⟨a, (k_edge_iff I B u v a).mp he, (notEnd_iff I B v).mp hn, hs, hb, hd, hm⟩
  · rintro ⟨a, he, hn, hs, hb, hd, hm⟩
    exact ⟨a, (k_edge_iff I B u v a).mpr he, (notEnd_iff I B v).mpr hn, hs, hb, hd, hm⟩

/-- Concrete finite labelled trace. The start may already be the original
initial state, so the empty trace is deliberately permitted. -/
inductive Trace (I : Instance k) (B : Reference k) (u : Pos B) (q : Fin k) :
    List (Bool × Fin k) → Pos B → Fin k → Prop
  | nil (hu : u.val < B.word.length) : Trace I B u q [] u q
  | snoc {ext : List (Bool × Fin k)} {v w : Pos B} {p r : Fin k}
      (prior : Trace I B u q ext v p) (a : Bool)
      (advance : RankQuery.advance B.word v.val a = w.val)
      (inside : w.val < B.word.length)
      (transition : step I r a = some p)
      (safe : I.bad.get r = false)
      (diagonal : (I.flags.get r).get r = false)
      (clear : (mask I B w.val).get r = false) :
      Trace I B u q (ext ++ [(a,r)]) w r

/-- A trace is an actual run of the existing finishing observer. -/
theorem trace_run (I : Instance k) (B : Reference k) (q0 : Fin k)
    {u v : Pos B} {q p : Fin k} {ext : List (Bool × Fin k)}
    (h : Trace I B u q ext v p) :
    Run (prefixGraph I B) (finishObserver I q0) (u,q) (v,p) := by
  induction h with
  | nil hu =>
    exact Run.refl ((finish_allowed_iff I q0 _ _).mpr ((notEnd_iff I B _).mpr hu))
  | snoc _ a he hi hs hb hd hm ih =>
    exact Run.step ih ((prefix_step_iff I B q0 _ _ _ _).mpr ⟨a,he,hi,hs,hb,hd,hm⟩)

/-- Every observer run has a finite labelled trace, with no length cutoff. -/
theorem trace_of_run (I : Instance k) (B : Reference k) (q0 : Fin k)
    {x y : Node (prefixGraph I B) (finishObserver I q0)}
    (h : Run (prefixGraph I B) (finishObserver I q0) x y) :
    ∃ ext : List (Bool × Fin k), Trace I B x.1 x.2 ext y.1 y.2 := by
  induction h with
  | refl hx =>
    exact ⟨[], Trace.nil ((notEnd_iff I B _).mp ((finish_allowed_iff I q0 _ _).mp hx))⟩
  | @step y z _ hs ih =>
    obtain ⟨ext, ht⟩ := ih
    obtain ⟨a, he, hi, hs, hb, hd, hm⟩ := (prefix_step_iff I B q0 _ _ _ _).mp hs
    refine ⟨ext ++ ([(a, (show Fin k from z.2))] : List (Bool × Fin k)), ?_⟩
    exact Trace.snoc ht a he hi hs hb hd hm

theorem run_iff_trace (I : Instance k) (B : Reference k) (q0 q p : Fin k)
    (u v : Pos B) :
    Run (prefixGraph I B) (finishObserver I q0) (u,q) (v,p) ↔
      ∃ ext : List (Bool × Fin k), Trace I B u q ext v p := by
  constructor
  · exact trace_of_run I B q0
  · rintro ⟨ext, h⟩
    exact trace_run I B q0 h

/-- The emitted word really follows the ORIGINAL machine when reversed. -/
theorem trace_reverse_run {I : Instance k} {B : Reference k}
    {u v : Pos B} {q p : Fin k} {ext : List (Bool × Fin k)}
    (h : Trace I B u q ext v p) :
    Subtail.runFrom I p (ext.map Prod.fst).reverse = some q := by
  induction h with
  | nil _ => rfl
  | snoc _ a he hi hs hb hd hm ih =>
    simpa [Subtail.runFrom, hs] using ih

/-- A trace's computed cursor has the advertised endpoint. -/
theorem trace_cursor {I : Instance k} {B : Reference k}
    {u v : Pos B} {q p : Fin k} {ext : List (Bool × Fin k)}
    (h : Trace I B u q ext v p) :
    RankQuerySound.walkTo B u.val (ext.map Prod.fst) = v.val := by
  induction h with
  | nil _ => rfl
  | snoc _ a he hi hs hb hd hm ih =>
    simp only [List.map_append, List.map_cons, List.map_nil,
      RankQuerySound.walkTo_append, ih, RankQuerySound.walkTo]
    exact he

/-- This is literally one clause of the existing finishQuery, not a new query
language or a replacement finishing condition. -/
def finishClause (I : Instance k) (q : Fin k) : Clause k :=
  { vars := 3
    tests := [(⟨0, by omega⟩, fun c => c.isEnd && decide (c.state = q))]
    equal := []
    unequal := []
    atoms := [⟨oneEdge .F, ⟨0, by omega⟩, ⟨1, by omega⟩⟩,
              ⟨finishObserver I q, ⟨1, by omega⟩, ⟨2, by omega⟩⟩] }

theorem finishQuery_eq (I : Instance k) :
    finishQuery I = (List.finRange k).map (finishClause I) := rfl

/-- The one-edge atom has its literal one-edge semantics in this direction. -/
theorem one_edge_accepts (G : Graph k) (l : Label) {u v : Fin G.size}
    (he : G.edge u l = some v) : Accepts G (oneEdge l) u v := by
  let q0 : Fin (oneEdge l).size := ⟨0, by change (0 : Nat) < 2; omega⟩
  let q1 : Fin (oneEdge l).size := ⟨1, by change (1 : Nat) < 2; omega⟩
  refine ⟨q0, List.mem_cons_self .., q1, List.mem_cons_self .., ?_⟩
  have hstart : Allowed G (oneEdge l) (u,q0) := rfl
  refine Run.step (Run.refl hstart) ?_
  refine ⟨l, he, ?_, rfl⟩
  change q1 ∈ (if (0 : Nat) = 0 ∧ l = l then [q1] else [])
  rw [if_pos (show (0 : Nat) = 0 ∧ l = l from ⟨rfl,rfl⟩)]
  exact List.mem_cons_self ..

/-- Remove exactly the syntactic existential-variable packaging of one clause. -/
theorem finish_clause_iff (I : Instance k) (G : Graph k) (q : Fin k) :
    SatClause G (finishClause I q) ↔
      ∃ e f x : Fin G.size, (G.colour e).isEnd = true ∧
        (G.colour e).state = q ∧ G.edge e .F = some f ∧
        Run G (finishObserver I q) (f,q) (x,I.initial) := by
  constructor
  · rintro ⟨σ, ht, _, _, ha⟩
    have ht0 := ht _ (List.mem_cons_self ..)
    change (G.colour (σ (⟨0, by omega⟩ : Fin 3))).isEnd &&
      decide ((G.colour (σ (⟨0, by omega⟩ : Fin 3))).state = q) = true at ht0
    obtain ⟨hend, hstate⟩ := Bool.and_eq_true.mp ht0
    have hF := RankQuerySound.accepts_oneEdge (ha _ (List.mem_cons_self ..))
    have hfinish := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain ⟨q', hq', p', hp', hr⟩ := hfinish
    change q' ∈ [q] at hq'
    change p' ∈ [I.initial] at hp'
    have heq := List.mem_singleton.mp hq'
    have hep := List.mem_singleton.mp hp'
    subst q'
    subst p'
    exact ⟨σ (⟨0,by omega⟩ : Fin 3), σ (⟨1,by omega⟩ : Fin 3), σ (⟨2,by omega⟩ : Fin 3),
      hend, of_decide_eq_true hstate, hF, hr⟩
  · rintro ⟨e, f, x, hend, hstate, hF, hr⟩
    let σ : Fin 3 → Fin G.size := fun i => if i.val = 0 then e else if i.val = 1 then f else x
    refine ⟨σ, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have ht' := List.mem_singleton.mp ht
      subst t
      simp [σ, hend, hstate]
    · intro z hz
      cases hz
    · intro z hz
      cases hz
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · change Accepts G (oneEdge .F) (σ (⟨0,by omega⟩ : Fin 3)) (σ (⟨1,by omega⟩ : Fin 3))
        simpa [σ] using one_edge_accepts G .F hF
      · rcases List.mem_cons.mp ha with rfl | ha
        · change Accepts G (finishObserver I q) (σ (⟨1,by omega⟩ : Fin 3)) (σ (⟨2,by omega⟩ : Fin 3))
          refine ⟨q, List.mem_cons_self .., I.initial, List.mem_cons_self .., ?_⟩
          simpa [σ] using hr
        · cases ha

/-- The actual finishing query chooses a path from the old failure parent,
with the reference's endpoint state as the current original state. -/
theorem sat_finish_iff_run (I : Instance k) (B : Reference k) :
    Sat (prefixGraph I B) (finishQuery I) ↔
      ∃ v : Pos B, Run (prefixGraph I B) (finishObserver I (B.label B.word.length))
        (parent B, B.label B.word.length) (v,I.initial) := by
  constructor
  · rintro ⟨c, hc, hs⟩
    rw [finishQuery_eq] at hc
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨e, f, v, hend, hstate, hF, hr⟩ := (finish_clause_iff I _ q).mp hs
    have he : e = endpoint B := Fin.ext (of_decide_eq_true hend)
    subst e
    change B.label B.word.length = q at hstate
    subst q
    rw [end_edge] at hF
    have hf : f = parent B := (Option.some.inj hF).symm
    subst f
    exact ⟨v,hr⟩
  · rintro ⟨v, hr⟩
    refine ⟨finishClause I (B.label B.word.length), ?_, ?_⟩
    · rw [finishQuery_eq]
      exact List.mem_map.mpr ⟨B.label B.word.length, List.mem_finRange _, rfl⟩
    · apply (finish_clause_iff I _ _).mpr
      exact ⟨endpoint B, parent B, v, by simp [prefixGraph,endpoint], rfl, end_edge I B, hr⟩

/-- Exact all-length finishing semantics: one finite labelled cursor trace.
This does not identify an arbitrary safe completion with a no-return finish. -/
theorem sat_finish_iff_trace (I : Instance k) (B : Reference k) :
    Sat (prefixGraph I B) (finishQuery I) ↔
      ∃ (ext : List (Bool × Fin k)) (v : Pos B),
        Trace I B (parent B) (B.label B.word.length) ext v I.initial := by
  rw [sat_finish_iff_run]
  constructor
  · rintro ⟨v, hr⟩
    obtain ⟨ext, ht⟩ := trace_of_run I B _ hr
    exact ⟨ext,v,ht⟩
  · rintro ⟨ext, v, ht⟩
    exact ⟨v,trace_run I B _ ht⟩

/-- The unchanged finite query decision is exact for the unbounded trace question. -/
theorem finish_check_correct (I : Instance k) (B : Reference k) :
    satCheck (prefixGraph I B) (finishQuery I) = true ↔
      ∃ (ext : List (Bool × Fin k)) (v : Pos B),
        Trace I B (parent B) (B.label B.word.length) ext v I.initial := by
  rw [satCheck_correct, sat_finish_iff_trace]

end RankQueryFinishTrace
end Subtail

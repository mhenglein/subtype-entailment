import Subtail.RankQueryFinishFacts
import Subtail.RankQueryFirstReturn

/-!
# Exact finishing-query trace semantics

Uses the EXISTING finishQuery, prefixGraph, observer run and original machine.
A trace records actual letters and reverse states. Every cursor stays strictly
below the reference endpoint. No compiler-closure, global witness bound, or
arbitrary-completion equivalence is assumed. The maximal-rank corollary derives
no-return from actual word ranks; the main equivalence uses literal no-return
completion. This module does not import the compiler or its soundness proof.
-/
namespace Subtail
namespace RankQueryFinishTrace
open TerminalRank RankMilestones RankQuery RankQueryFinishFacts

variable {k : Nat}

abbrev Pos (B : Reference k) := Fin (B.word.length + 1)

def endpoint (B : Reference k) : Pos B := ⟨B.word.length, Nat.lt_succ_self _⟩

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

/-- Concrete finite labelled trace; an empty completion is permitted. -/
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

theorem trace_run (I : Instance k) (B : Reference k) (q0 : Fin k)
    {u v : Pos B} {q p : Fin k} {ext : List (Bool × Fin k)}
    (h : Trace I B u q ext v p) :
    Run (prefixGraph I B) (finishObserver I q0) (u,q) (v,p) := by
  induction h with
  | nil hu =>
    exact Run.refl ((finish_allowed_iff I q0 _ _).mpr ((notEnd_iff I B _).mpr hu))
  | snoc _ a he hi hs hb hd hm ih =>
    exact Run.step ih ((prefix_step_iff I B q0 _ _ _ _).mpr ⟨a,he,hi,hs,hb,hd,hm⟩)

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

/-- The literal repeated-K walk, using the pinned advance function. -/
def walkTo (B : Reference k) (v : Nat) : List Bool → Nat
  | [] => v
  | a :: rest => walkTo B (RankQuery.advance B.word v a) rest

theorem walkTo_append (B : Reference k) (v : Nat) (a b : List Bool) :
    walkTo B v (a ++ b) = walkTo B (walkTo B v a) b := by
  induction a generalizing v with
  | nil => rfl
  | cons c a ih => simp only [List.cons_append, walkTo, ih]

theorem trace_cursor {I : Instance k} {B : Reference k}
    {u v : Pos B} {q p : Fin k} {ext : List (Bool × Fin k)}
    (h : Trace I B u q ext v p) :
    walkTo B u.val (ext.map Prod.fst) = v.val := by
  induction h with
  | nil _ => rfl
  | snoc _ a he hi hs hb hd hm ih =>
    simp only [List.map_append, List.map_cons, List.map_nil,
      walkTo_append, ih, walkTo]
    exact he

/-- Literally one clause of finishQuery, not a replacement query. -/
def finishClause (I : Instance k) (q : Fin k) : Clause k :=
  { vars := 3
    tests := [(⟨0, by omega⟩, fun c => c.isEnd && decide (c.state = q))]
    equal := []
    unequal := []
    atoms := [⟨oneEdge .F, ⟨0, by omega⟩, ⟨1, by omega⟩⟩,
              ⟨finishObserver I q, ⟨1, by omega⟩, ⟨2, by omega⟩⟩] }

theorem finishQuery_eq (I : Instance k) :
    finishQuery I = (List.finRange k).map (finishClause I) := rfl

/-- Every move of a one-edge observer goes from 0 to 1 on its one label. -/
theorem oneEdge_move (l : Label) {q p : Fin (oneEdge (k := k) l).size}
    {c d : Colour k} {a : Label}
    (h : p ∈ (oneEdge l).move q c a d) :
    q.val = 0 ∧ p.val = 1 ∧ a = l := by
  simp only [oneEdge] at h
  split at h
  · rename_i hc
    have hp := List.mem_singleton.mp h
    exact ⟨hc.1, congrArg Fin.val hp, hc.2⟩
  · cases h

/-- With controls 0->1 only, every nonempty run is exactly one step. -/
theorem oneEdge_run {G : Graph k} {l : Label}
    {x y : Node G (oneEdge l)} (h : Run G (oneEdge l) x y) :
    y = x ∨ (G.edge x.1 l = some y.1 ∧ x.2.val = 0 ∧ y.2.val = 1) := by
  induction h with
  | refl _ => exact Or.inl rfl
  | @step y z _ hs ih =>
    obtain ⟨a, he, hm, _⟩ := hs
    obtain ⟨hy, hz, rfl⟩ := oneEdge_move l hm
    rcases ih with hxy | ⟨_, _, hy'⟩
    · subst y
      exact Or.inr ⟨he,hy,hz⟩
    · omega

theorem accepts_oneEdge {G : Graph k} {l : Label} {u v : Fin G.size}
    (h : Accepts G (oneEdge l) u v) : G.edge u l = some v := by
  obtain ⟨q,hq,p,hp,hr⟩ := h
  have hqv : q.val = 0 := congrArg Fin.val (List.mem_singleton.mp hq)
  have hpv : p.val = 1 := congrArg Fin.val (List.mem_singleton.mp hp)
  rcases oneEdge_run hr with heq | ⟨he,_,_⟩
  · have := congrArg (fun n : Node G (oneEdge l) => n.2.val) heq
    simp only at this
    omega
  · exact he

theorem one_edge_accepts (G : Graph k) (l : Label) {u v : Fin G.size}
    (he : G.edge u l = some v) : Accepts G (oneEdge l) u v := by
  let q0 : Fin (oneEdge (k := k) l).size := ⟨0, by change (0 : Nat) < 2; omega⟩
  let q1 : Fin (oneEdge (k := k) l).size := ⟨1, by change (1 : Nat) < 2; omega⟩
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
    change ((G.colour (σ (⟨0, by omega⟩ : Fin 3))).isEnd &&
      decide ((G.colour (σ (⟨0, by omega⟩ : Fin 3))).state = q)) = true at ht0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht0
    obtain ⟨hend, hstate⟩ := ht0
    have hF := accepts_oneEdge (ha _ (List.mem_cons_self ..))
    have hfinish := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain ⟨q', hq', p', hp', hr⟩ := hfinish
    change q' ∈ [q] at hq'
    change p' ∈ [I.initial] at hp'
    have heq := List.mem_singleton.mp hq'
    have hep := List.mem_singleton.mp hp'
    subst q'
    subst p'
    exact ⟨σ (⟨0,by omega⟩ : Fin 3), σ (⟨1,by omega⟩ : Fin 3), σ (⟨2,by omega⟩ : Fin 3),
      hend, hstate, hF, hr⟩
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

/-- Exact finite-query packaging of the finishing observer run. -/
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

/-- Exact all-length semantics: one finite labelled cursor trace. -/
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

/-- The unchanged finite query decision exactly decides the unbounded trace question. -/
theorem finish_check_correct (I : Instance k) (B : Reference k) :
    satCheck (prefixGraph I B) (finishQuery I) = true ↔
      ∃ (ext : List (Bool × Fin k)) (v : Pos B),
        Trace I B (parent B) (B.label B.word.length) ext v I.initial := by
  rw [satCheck_correct, sat_finish_iff_trace]

/-! ## From a complete safe reverse reference to the original Witness -/

/-- Reading any finite slice backwards follows the reference's actual labels. -/
theorem reference_slice_run (I : Instance k) (B : Reference k)
    (hrun : ∀ j, (hj : j < B.word.length) →
      step I (B.label (j+1)) (B.word[j]'hj) = some (B.label j)) :
    ∀ n j, j+n ≤ B.word.length →
      runFrom I (B.label (j+n)) ((B.word.drop j).take n).reverse = some (B.label j) := by
  intro n
  induction n with
  | zero => intro j hj; simp [runFrom]
  | succ n ih =>
    intro j hj
    have hn : n < (B.word.drop j).length := by simp only [List.length_drop]; omega
    have hjn : j+n < B.word.length := by omega
    rw [List.take_succ_eq_append_getElem hn, List.reverse_append]
    have he : (B.word.drop j)[n] = B.word[j+n] := by simp [List.getElem_drop]
    rw [he]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, runFrom]
    rw [show j+(n+1)=j+n+1 from by omega, hrun (j+n) hjn]
    simpa only [Option.bind_some] using ih j (by omega)

/-- A reversed reference suffix is an actual original-machine run. -/
theorem reference_drop_run (I : Instance k) (B : Reference k)
    (hB : SafeReference I B) {j : Nat} (hj : j ≤ B.word.length) :
    runFrom I (B.label B.word.length) (B.word.drop j).reverse = some (B.label j) := by
  have hh := reference_slice_run I B hB.run (B.word.length-j) j (by omega)
  have he : j+(B.word.length-j)=B.word.length := by omega
  rw [he, List.take_of_length_le (by simp)] at hh
  exact hh

/-- Every forward cut has the reference's intended original state. -/
theorem reference_forward_cut (I : Instance k) (B : Reference k)
    (hB : SafeReference I B) (hstart : B.label B.word.length = I.initial)
    {i : Nat} (_hi : i ≤ B.word.length) :
    Subtail.stateAt I B.word.reverse i = some (B.label (B.word.length-i)) := by
  unfold Subtail.stateAt
  rw [List.take_reverse, ← hstart]
  exact reference_drop_run I B hB (Nat.sub_le _ _)

/-- Every literal border of a safe reference cut has an unflagged original pair. -/
theorem reference_border_clear (I : Instance k) (B : Reference k)
    (hB : SafeReference I B) {j h : Nat} (hj : j ≤ B.word.length)
    (hh : h ∈ borderLengths (B.word.take j)) :
    (I.flags.get (B.label j)).get (B.label h) = false := by
  have hc := hB.border j hj
  have hm : (mask I B j).get (B.label j) = ((borderLengths (B.word.take j)).any
    fun h => (I.flags.get (B.label j)).get (B.label h)) := by
    simp [mask, Vector.get] <;> rfl
  rw [hm] at hc
  have hn := (List.any_eq_false.mp hc) h hh
  cases hf : (I.flags.get (B.label j)).get (B.label h) with
  | false => rfl
  | true => exact False.elim (hn hf)

/-- Safety of the complete labelled reverse word implies the EXISTING direct
Witness predicate, including empty and diagonal suffix comparisons. -/
theorem safe_reference_witness (I : Instance k) (B : Reference k)
    (hB : SafeReference I B) (hstart : B.label B.word.length = I.initial) :
    Witness I B.word.reverse := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ≤ B.word.length := by simpa only [List.length_reverse] using hi
    rw [reference_forward_cut I B hB hstart hi']
    simp only [safeCheck, hB.safe _ (Nat.sub_le _ _)]
    rfl
  · have he := reference_forward_cut I B hB hstart (i := B.word.length) (Nat.le_refl _)
    simp only [List.length_reverse, he, Nat.sub_self, finalCheck]
    exact hB.accepting
  · intro j hj i hij hag
    have hj' : j ≤ B.word.length := by simpa only [List.length_reverse] using hj
    have hi' : i ≤ B.word.length := by omega
    have hs : (B.word.take (B.word.length-j)).IsSuffix (B.word.take (B.word.length-i)) := by
      change (B.word.reverse.drop j).IsPrefix (B.word.reverse.drop i) at hag
      rw [List.drop_reverse, List.drop_reverse, List.reverse_prefix] at hag
      exact hag
    have hb : B.word.length-j ∈ borderLengths (B.word.take (B.word.length-i)) := by
      apply mem_borderLengths.mpr
      have hjle : B.word.length-j ≤ B.word.length-i := by omega
      have he := List.suffix_iff_eq_drop.mp hs
      simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)] at he
      refine ⟨by simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]; omega, ?_⟩
      simpa only [List.take_take, Nat.min_eq_left hjle, List.length_take,
        Nat.min_eq_left (Nat.sub_le _ _)] using he
    have hf := reference_border_clear I B hB (Nat.sub_le _ _) hb
    rw [reference_forward_cut I B hB hstart hi', reference_forward_cut I B hB hstart hj']
    simp only [unflaggedCheck, hf]
    rfl

/-! ## A finishing trace reconstructs one complete safe reference -/

/-- Append one bit with its actual reverse-run state. -/
def appendLetter (B : Reference k) (a : Bool) (p : Fin k) : Reference k where
  word := B.word ++ [a]
  label := fun j => if j ≤ B.word.length then B.label j else p

/-- Append a finite labelled word by actual one-letter extensions. -/
def extend (B : Reference k) (ext : List (Bool × Fin k)) : Reference k :=
  ext.foldl (fun C e => appendLetter C e.1 e.2) B

theorem extend_nil (B : Reference k) : extend B [] = B := rfl

theorem extend_snoc (B : Reference k) (ext : List (Bool × Fin k)) (a : Bool) (p : Fin k) :
    extend B (ext ++ [(a,p)]) = appendLetter (extend B ext) a p := by
  simp only [extend, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem extend_word (B : Reference k) (ext : List (Bool × Fin k)) :
    (extend B ext).word = B.word ++ ext.map Prod.fst := by
  suffices ∀ (ext : List (Bool × Fin k)) (B : Reference k),
      (extend B ext).word = B.word ++ ext.map Prod.fst by exact this ext B
  intro ext
  induction ext with
  | nil => intro B; simp [extend]
  | cons e ext ih =>
    intro B
    change (extend (appendLetter B e.1 e.2) ext).word = _
    rw [ih]
    simp [appendLetter]

theorem extend_label_old (B : Reference k) (ext : List (Bool × Fin k)) {j : Nat}
    (hj : j ≤ B.word.length) : (extend B ext).label j = B.label j := by
  induction ext generalizing B with
  | nil => rfl
  | cons e ext ih =>
    change (extend (appendLetter B e.1 e.2) ext).label j = B.label j
    rw [ih (appendLetter B e.1 e.2) (by simp only [appendLetter, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp [appendLetter, hj]

/-- Literal labelled-prefix relation used only to prove mask preservation. -/
def Extends (B C : Reference k) : Prop :=
  B.word <+: C.word ∧ ∀ j, j ≤ B.word.length → C.label j = B.label j

theorem extend_extends (B : Reference k) (ext : List (Bool × Fin k)) : Extends B (extend B ext) := by
  refine ⟨?_, fun j hj => extend_label_old B ext hj⟩
  rw [extend_word]
  exact List.prefix_append _ _

theorem appendLetter_extends (B : Reference k) (a : Bool) (p : Fin k) :
    Extends B (appendLetter B a p) := by
  exact ⟨List.prefix_append _ _, fun j hj => by simp [appendLetter,hj]⟩

theorem Extends.trans {B C D : Reference k} (hBC : Extends B C) (hCD : Extends C D) :
    Extends B D := by
  refine ⟨hBC.1.trans hCD.1, ?_⟩
  intro j hj
  rw [hCD.2 j (Nat.le_trans hj hBC.1.length_le), hBC.2 j hj]

/-- Boolean folds depend only on elements actually in the list. -/
theorem any_eq_on {α : Type} {xs : List α} {f g : α → Bool}
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Prefix masks are literally unchanged when both word and labels extend. -/
theorem extends_mask {B C : Reference k} (h : Extends B C) (I : Instance k)
    {j : Nat} (hj : j ≤ B.word.length) : mask I C j = mask I B j := by
  have ht0 : C.word.take B.word.length = B.word := (List.prefix_iff_eq_take.mp h.1).symm
  have ht : C.word.take j = B.word.take j := by
    simpa only [List.take_take, Nat.min_eq_left hj] using congrArg (fun w : Word => w.take j) ht0
  apply Vector.ext
  intro p hp
  have hget : (mask I C j).get ⟨p,hp⟩ = (mask I B j).get ⟨p,hp⟩ := by
    rw [RankQueryFirstReturn.mask_get_eq, RankQueryFirstReturn.mask_get_eq]
    unfold FirstReturnGraph.mask
    rw [ht]
    apply any_eq_on
    intro b hb
    have hh := (mem_borderLengths.mp hb).1
    have hb' : b ≤ B.word.length := by simp only [List.length_take] at hh; omega
    rw [h.2 b hb']
  simpa [Vector.get] using hget

/-- Appending a letter preserves safety when its new full mask is clear. -/
theorem safe_appendLetter (I : Instance k) (C : Reference k) (a : Bool) (p : Fin k)
    (hC : SafeReference I C) (hs : step I p a = some (C.label C.word.length))
    (hb : I.bad.get p = false)
    (hm : (mask I (appendLetter C a p) (appendLetter C a p).word.length).get p = false) :
    SafeReference I (appendLetter C a p) := by
  let D := appendLetter C a p
  have hlen : D.word.length = C.word.length+1 := by simp [D,appendLetter]
  have hp : D.label D.word.length = p := by
    change (if (C.word ++ [a]).length ≤ C.word.length then C.label (C.word ++ [a]).length else p) = p
    rw [if_neg (by simp)]
  have hE : Extends C D := appendLetter_extends C a p
  change SafeReference I D
  refine ⟨by rw [hlen]; omega, ?_, ?_, ?_, ?_⟩
  · rw [hE.2 0 (Nat.zero_le _)]
    exact hC.accepting
  · intro j hj
    by_cases hlt : j < C.word.length
    · have hw : D.word[j]'hj = C.word[j]'hlt := by
        exact List.getElem_append_left hlt
      rw [hE.2 (j+1) (by omega), hE.2 j (by omega), hw]
      exact hC.run j hlt
    · have he : j = C.word.length := by omega
      subst j
      have hd : D.word[C.word.length]'hj = a := by simp [D,appendLetter]
      rw [show C.word.length+1 = D.word.length from hlen.symm, hp,
        hE.2 C.word.length (Nat.le_refl _), hd]
      exact hs
  · intro j hj
    by_cases hle : j ≤ C.word.length
    · rw [hE.2 j hle]
      exact hC.safe j hle
    · have he : j = D.word.length := by omega
      rw [he,hp]
      exact hb
  · intro j hj
    by_cases hle : j ≤ C.word.length
    · rw [hE.2 j hle, extends_mask hE I hle]
      exact hC.border j hle
    · have he : j = D.word.length := by omega
      rw [he,hp]
      exact hm

/-- The local finishing step computes the NEW proper-border parent even though
it never returns to the whole old reference. -/
theorem append_parent {B C : Reference k} (hE : Extends B C)
    (hpos : 0 < C.word.length) {v : Nat} (hp : failureParent C.word = v)
    (hv : v < B.word.length) (a : Bool) (p : Fin k) :
    failureParent (appendLetter C a p).word = RankQuery.advance B.word v a := by
  let D := appendLetter C a p
  have hdlen : D.word.length = C.word.length+1 := by simp [D,appendLetter]
  have hn : FirstReturnGraph.Next D.word C.word.length a := by
    unfold FirstReturnGraph.Next
    rw [← hdlen, List.take_length]
    simp [D,appendLetter]
  have h := FirstReturnGraph.parent_next hpos hn
  have ht : D.word.take C.word.length = C.word := by simp [D,appendLetter]
  have htfull : D.word.take (C.word.length+1) = D.word := by rw [← hdlen,List.take_length]
  rw [htfull, ht, hp] at h
  have hBD : Extends B D := hE.trans (appendLetter_extends C a p)
  have htake : D.word.take B.word.length = B.word := (List.prefix_iff_eq_take.mp hBD.1).symm
  rw [← FirstReturnGraph.advance_prefix hv, htake] at h
  rw [← RankQueryFirstReturn.advance_eq (Nat.le_of_lt hv)] at h
  exact h

/-- Complete safety and exact original endpoint of the reference reconstructed
from a no-return finishing trace. -/
theorem trace_safe_reference (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    {ext : List (Bool × Fin k)} {v : Pos B} {p : Fin k}
    (h : Trace I B (parent B) (B.label B.word.length) ext v p) :
    SafeReference I (extend B ext) ∧
      failureParent (extend B ext).word = v.val ∧
      (extend B ext).label (extend B ext).word.length = p := by
  induction h with
  | nil hu => exact ⟨hB,rfl,rfl⟩
  | @snoc ext v w p r ht a ha hi hs hb hd hm ih =>
    obtain ⟨hC,hparent,hlabel⟩ := ih
    let C := extend B ext
    let D := appendLetter C a r
    have hBC : Extends B C := extend_extends B ext
    have hv : v.val < B.word.length := (notEnd_iff I B v).mp
      ((finish_run_notEnd I (B.label B.word.length) (trace_run I B _ ht)).2)
    have hpar : failureParent D.word = w.val :=
      (append_parent hBC hC.nonempty hparent hv a r).trans ha
    have hBD := hBC.trans (appendLetter_extends C a r)
    have hnewlabel : D.label D.word.length = r := by
      change (if (C.word ++ [a]).length ≤ C.word.length then C.label (C.word ++ [a]).length else r) = r
      rw [if_neg (by simp)]
    have hmask : (mask I D D.word.length).get r = false := by
      rw [RankQueryFirstReturn.mask_get_eq]
      rw [FirstReturnGraph.mask_decomposition (Nat.le_refl _) (by simp [D,appendLetter])]
      rw [List.take_length,hpar,hnewlabel]
      rw [← RankQueryFirstReturn.mask_get_eq, extends_mask hBD I (Nat.le_of_lt hi)]
      rw [hd,hm]
      rfl
    have hsafe : SafeReference I D :=
      safe_appendLetter I C a r hC (by rwa [hlabel]) hb hmask
    rw [extend_snoc]
    exact ⟨hsafe,hpar,hnewlabel⟩

/-- Sound finishing: a model of the existing Finish query reconstructs a
DIRECT original Witness. No closure theorem or rank bound is assumed. -/
theorem finish_implies_witness (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    (h : Sat (prefixGraph I B) (finishQuery I)) :
    ∃ ext : List (Bool × Fin k), Witness I (B.word ++ ext.map Prod.fst).reverse := by
  obtain ⟨ext,v,ht⟩ := (sat_finish_iff_trace I B).mp h
  obtain ⟨hs,_,he⟩ := trace_safe_reference I B hB ht
  have hw := safe_reference_witness I (extend B ext) hs he
  exact ⟨ext, by simpa only [extend_word] using hw⟩

/-! ## Completeness for the literal no-further-return continuation -/

/-- Literal no-return condition, including a return at the ultimate cut. -/
def NoReturn (B C : Reference k) : Prop :=
  ∀ j, B.word.length < j → j ≤ C.word.length →
    B.word.length ∉ borderLengths (C.word.take j)

/-- No later copy of the old prefix forces every fresh failure parent to be
strictly smaller than the old reference. This is a word theorem, not a cursor
assumption. -/
theorem noReturn_parent_lt {B C : Reference k} (hno : NoReturn B C)
    {j : Nat} (hmj : B.word.length < j) (hj : j ≤ C.word.length) :
    failureParent (C.word.take j) < B.word.length := by
  have hlen : (C.word.take j).length = j := List.length_take_of_le hj
  have hs := failureParent_spec (C.word.take j) (by omega)
  have hp : failureParent (C.word.take j) < j := by omega
  by_cases h : failureParent (C.word.take j) < B.word.length
  · exact h
  · have hm : B.word.length ≤ failureParent (C.word.take j) := by omega
    let e := j - failureParent (C.word.take j) + B.word.length
    exact False.elim (hno e (by dsimp [e]; omega) (by dsimp [e]; omega)
      (shifted_border hj hs.1 hm))

/-- Finishing traces really have no later literal full return. -/
theorem trace_noReturn (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    {ext : List (Bool × Fin k)} {v : Pos B} {p : Fin k}
    (h : Trace I B (parent B) (B.label B.word.length) ext v p) :
    NoReturn B (extend B ext) := by
  induction h with
  | nil _ => intro j hj hb; simp only [extend_nil] at hb; omega
  | @snoc ext v w p r ht a ha hi hs hb hd hm ih =>
    intro j hj hle
    rw [extend_snoc] at hle ⊢
    let C := extend B ext
    have hlen : (appendLetter C a r).word.length = C.word.length+1 := by simp [appendLetter]
    by_cases hold : j ≤ C.word.length
    · have htake : (appendLetter C a r).word.take j = C.word.take j :=
        List.take_append_of_le_length hold
      rw [htake]
      exact ih j hj hold
    · have he : j = (appendLetter C a r).word.length := by change j ≤ (appendLetter C a r).word.length at hle; omega
      rw [he,List.take_length]
      have ht' := Trace.snoc ht a ha hi hs hb hd hm
      have hpar := (trace_safe_reference I B hB ht').2.1
      rw [extend_snoc] at hpar
      have hp := failureParent_spec (appendLetter C a r).word (by rw [hlen]; omega)
      intro hborder
      have hm := hp.2.2 B.word.length hborder (by omega)
      change failureParent (appendLetter C a r).word = w.val at hpar
      omega

/-- Construct one finite labelled trace by walking through the given completion.
The quantified no-return property is checked on the ACTUAL completed word. -/
theorem trace_from_completion (I : Instance k) (B C : Reference k)
    (hB : SafeReference I B) (hC : SafeReference I C) (hBC : Extends B C)
    (hno : NoReturn B C) :
    ∀ d, B.word.length+d ≤ C.word.length →
      ∃ (ext : List (Bool × Fin k)) (v : Pos B),
        Trace I B (parent B) (B.label B.word.length) ext v (C.label (B.word.length+d)) ∧
        v.val = failureParent (C.word.take (B.word.length+d)) ∧
        ext.map Prod.fst = (C.word.drop B.word.length).take d := by
  have htake : C.word.take B.word.length = B.word := (List.prefix_iff_eq_take.mp hBC.1).symm
  intro d
  induction d with
  | zero =>
    intro hd
    have hp := (failureParent_spec B.word hB.nonempty).2.1
    refine ⟨[],parent B,?_,?_,rfl⟩
    · rw [Nat.add_zero,hBC.2 _ (Nat.le_refl _)]
      exact Trace.nil hp
    · simp [parent,htake]
  | succ d ih =>
    intro hd
    obtain ⟨ext,v,ht,hv,hw⟩ := ih (by omega)
    let j := B.word.length+d
    have hj : j < C.word.length := by dsimp [j]; omega
    let a := C.word[j]
    let p := C.label (j+1)
    have hpl : failureParent (C.word.take (j+1)) < B.word.length :=
      noReturn_parent_lt hno (by dsimp [j]; omega) (by omega)
    let w : Pos B := ⟨failureParent (C.word.take (j+1)),by omega⟩
    have hvlt : v.val < B.word.length := (notEnd_iff I B v).mp
      ((finish_run_notEnd I (B.label B.word.length) (trace_run I B _ ht)).2)
    have ha : RankQuery.advance B.word v.val a = w.val := by
      have hn : FirstReturnGraph.Next C.word j a := by
        exact List.take_succ_eq_append_getElem hj
      have hp := FirstReturnGraph.parent_next (by dsimp [j]; have := hB.nonempty; omega) hn
      rw [← hv] at hp
      rw [← FirstReturnGraph.advance_prefix hvlt,htake,
        ← RankQueryFirstReturn.advance_eq (Nat.le_of_lt hvlt)] at hp
      exact hp.symm
    have hsafe := hC.safe (j+1) (by omega)
    have hmask := hC.border (j+1) (by omega)
    rw [RankQueryFirstReturn.mask_get_eq] at hmask
    rw [FirstReturnGraph.mask_decomposition (by omega) (by omega)] at hmask
    have hmask' : (I.flags.get p).get p = false ∧ (mask I B w.val).get p = false := by
      rw [← RankQueryFirstReturn.mask_get_eq,
        extends_mask hBC I (Nat.le_of_lt hpl)] at hmask
      exact Bool.or_eq_false_iff.mp hmask
    refine ⟨ext ++ [(a,p)],w,?_,rfl,?_⟩
    · change Trace I B (parent B) (B.label B.word.length) (ext ++ [(a,p)]) w p
      exact Trace.snoc ht a ha hpl (hC.run j hj) hsafe hmask'.1 hmask'.2
    · rw [List.map_append,hw,List.take_succ_eq_append_getElem (by simp only [List.length_drop]; omega)]
      simp [a,j,List.getElem_drop]

/-- The precise bidirectional finishing theorem. NoReturn is indispensable:
it is not replaced by arbitrary safe completion. -/
theorem finish_iff_no_return_completion (I : Instance k) (B : Reference k)
    (hB : SafeReference I B) :
    Sat (prefixGraph I B) (finishQuery I) ↔
      ∃ C : Reference k, SafeReference I C ∧ Extends B C ∧
        C.label C.word.length = I.initial ∧ NoReturn B C := by
  constructor
  · intro h
    obtain ⟨ext,v,ht⟩ := (sat_finish_iff_trace I B).mp h
    obtain ⟨hs,_,he⟩ := trace_safe_reference I B hB ht
    exact ⟨extend B ext,hs,extend_extends B ext,he,trace_noReturn I B hB ht⟩
  · rintro ⟨C,hC,hBC,hstart,hno⟩
    have hlen := hBC.1.length_le
    obtain ⟨ext,v,ht,_,_⟩ := trace_from_completion I B C hB hC hBC hno
      (C.word.length-B.word.length) (by omega)
    have he : B.word.length+(C.word.length-B.word.length)=C.word.length := by omega
    rw [he,hstart] at ht
    exact (sat_finish_iff_trace I B).mpr ⟨ext,v,ht⟩

/-- At a maximal-rank reference, every safe complete continuation satisfies
Finish. This discharges the no-return condition from the actual word ranks. -/
theorem maximal_rank_completion_finishes (I : Instance k) (B C : Reference k)
    (hB : SafeReference I B) (hC : SafeReference I C) (hBC : Extends B C)
    (hstart : C.label C.word.length = I.initial)
    (hmax : ∀ j, j ≤ C.word.length → rank (C.word.take j) ≤ rank B.word) :
    Sat (prefixGraph I B) (finishQuery I) := by
  apply (finish_iff_no_return_completion I B hB).mpr
  refine ⟨C,hC,hBC,hstart,?_⟩
  intro j hmj hj
  have htake : C.word.take B.word.length = B.word := (List.prefix_iff_eq_take.mp hBC.1).symm
  exact no_return_after_maximal_rank (by rw [htake]) hmax hmj hj

end RankQueryFinishTrace
end Subtail

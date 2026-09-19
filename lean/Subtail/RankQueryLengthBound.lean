import Subtail.RankQueryWeightBound
import Subtail.RankQueryDecision

/-!
# Bounded shared-interval reconstruction and an explicit terminal witness bound

A separate quantitative layer over the unchanged compiler and original Witness.
Paths are shortened only in the joint generator/observer product after boundary
controls and the common vertex assignment have been fixed.
-/
namespace Subtail.RankQueryLengthBound
open RankQuery RankQueryCompiler RankQueryEnumeration RankQuerySound

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {k : Nat}

/-- The existing run relation with an explicit number of edges. -/
inductive LengthRun (G : Graph k) (O : Observer k) (x : Node G O) : Nat -> Node G O -> Prop
  | refl (h : Allowed G O x) : LengthRun G O x 0 x
  | step {n : Nat} {y z : Node G O} (h : LengthRun G O x n y) (hs : Step G O y z) :
      LengthRun G O x (n + 1) z

theorem LengthRun.toRun {G : Graph k} {O : Observer k} {x y : Node G O} {n : Nat}
    (h : LengthRun G O x n y) : Run G O x y := by
  induction h with
  | refl h => exact Run.refl h
  | step _ hs ih => exact Run.step ih hs

theorem LengthRun.prepend {G : Graph k} {O : Observer k} {x y z : Node G O} {n : Nat}
    (hx : Allowed G O x) (hs : Step G O x y) (h : LengthRun G O y n z) :
    LengthRun G O x (n + 1) z := by
  induction h with
  | refl _ => exact LengthRun.step (LengthRun.refl hx) hs
  | step _ ht ih => exact LengthRun.step ih ht

theorem lengthRun_of_chain (G : Graph k) (O : Observer k) {x y : Node G O}
    {l : List (Node G O)} (hx : Allowed G O x) (hc : Chain G O (x :: l))
    (hl : (x :: l).getLast? = some y) : LengthRun G O x l.length y := by
  induction l generalizing x with
  | nil =>
    have he : x = y := Option.some.inj hl
    subst y
    exact LengthRun.refl hx
  | cons z l ih =>
    have hs : Step G O x z := hc.1
    have hz : Allowed G O z := by
      obtain ⟨_, _, _, hz⟩ := hs
      exact hz
    have ht := ih hz hc.2 (by simpa only [List.getLast?_cons_cons] using hl)
    exact LengthRun.prepend hx hs ht

theorem allNodes_length (G : Graph k) (O : Observer k) :
    (allNodes G O).length = G.size * O.size := by
  simp [allNodes, List.length_flatMap, List.map_const', List.sum_replicate_nat]

/-- A shortest product path retains the chosen endpoints and acceptance. -/
theorem accepts_length_bound (G : Graph k) (O : Observer k) {u v : Fin G.size}
    (h : Accepts G O u v) :
    ∃ q ∈ O.initial, ∃ p ∈ O.final, ∃ n,
      LengthRun G O (u, q) n (v, p) ∧ n + 1 <= G.size * O.size := by
  obtain ⟨q, hq, p, hp, l, hc, hl, hd, ha, _⟩ := accepts_bounded_visits G O h u
  have hlen := hd.length_le_of_subset (fun x _ => mem_allNodes G O x)
  rw [allNodes_length] at hlen
  exact ⟨q, hq, p, hp, l.length,
    lengthRun_of_chain G O (ha _ (by simp)) hc hl, by simpa using hlen⟩

/-- Strengthening run_gen: each emitted symbol corresponds to exactly one edge. -/
theorem lengthRun_gen (I : Instance k) (B : Reference k) (items : List (Active k))
    (ql : Fin k) (nl : Option Bool) (qr : Fin k) (nr : Option Bool)
    {x y : Node (prefixGraph I B) (intervalObs I items ql nl qr nr)} {n : Nat}
    (h : LengthRun (prefixGraph I B) (intervalObs I items ql nl qr nr) x n y) :
    ∃ (x0 x1 : IControl k) (ext : List (Bool × Fin k)),
      decodeI items x.2.val = some x0 ∧ decodeI items y.2.val = some x1 ∧
      Gen I B items x.1.val x0 ext y.1.val x1 ∧ ext.length = n := by
  induction h with
  | refl hx =>
    simp only [Allowed, intervalObs] at hx
    cases hd : decodeI items x.2.val with
    | none => simp [hd] at hx
    | some x0 =>
      simp only [hd] at hx
      exact ⟨x0, x0, [], rfl, rfl, Gen.nil hx, rfl⟩
  | @step n y' z' _ hs ih =>
    obtain ⟨x0, x1, ext, hd0, hd1, hg, hlen⟩ := ih
    obtain ⟨l, he, hm, hz⟩ := hs
    simp only [intervalObs, hd1] at hm
    have hm' := List.mem_filter.mp hm
    cases hd2 : decodeI items z'.2.val with
    | none => simp [hd2] at hm'
    | some x2 =>
      simp only [hd2] at hm'
      have hstep := hm'.2
      obtain ⟨b, hb, rfl⟩ := intervalStep_label hstep
      have hedge : z'.1.val = advance B.word y'.1.val b := by
        simp only [prefixGraph] at he
        exact (congrArg Fin.val (Option.some.inj he)).symm
      simp only [Allowed, intervalObs, hd2] at hz
      rw [prefixGraph_colour, prefixGraph_colour, hedge] at hstep
      rw [prefixGraph_colour, hedge] at hz
      exact ⟨x0, x2, ext ++ [(b, x2.state)], hd0, rfl,
        hedge ▸ gen_snoc hg hb hstep hz, by simp [hlen]⟩

/-- One shared trace with every observation and all boundary controls retained. -/
theorem interval_trace_bounded (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    {g : Nat} {u v : Fin (prefixGraph I B).size}
    (h : Accepts (prefixGraph I B) (intervalAtom I c D g).observer u v) :
    ∃ (x0 x1 : IControl k) (ext : List (Bool × Fin k)),
      Gen I B (itemsAt I c D g) u.val x0 ext v.val x1 ∧
      x0.state = markState D g ∧ x0.next = nextOf D g ∧ x0.seen = 0 ∧
      x0.controls = (itemsAt I c D g).map (fun a => a.2.1) ∧
      x1.state = markState D (g + 1) ∧ x1.next = nextOf D (g + 1) ∧ x1.seen = 1 ∧
      x1.controls = (itemsAt I c D g).map (fun a => a.2.2) ∧
      ext.length <= (B.word.length + 1) * (intervalAtom I c D g).observer.size := by
  obtain ⟨q, hq, p, hp, n, hr, hlen⟩ := accepts_length_bound _ _ h
  obtain ⟨x0, x1, ext, hd0, hd1, hg, hex⟩ := lengthRun_gen I B _ _ _ _ _ hr
  obtain ⟨y0, hy0, hs0, hn0, hseen0, hc0⟩ := interval_initial_spec hq
  obtain ⟨y1, hy1, hs1, hn1, hseen1, hc1⟩ := interval_final_spec hp
  have e0 : y0 = x0 := Option.some.inj (hy0.symm.trans hd0)
  have e1 : y1 = x1 := Option.some.inj (hy1.symm.trans hd1)
  subst e0 e1
  exact ⟨y0, y1, ext, hg, hs0, hn0, hseen0, hc0, hs1, hn1, hseen1, hc1, by
    change n + 1 <= (B.word.length + 1) * _ at hlen
    omega⟩

/-- Replace only interval traces, keeping the common assignment and every seam. -/
theorem exists_bounded_recon (I : Instance k) (c : Clause k) (D : Diagram k)
    (B : Reference k) {sigma : Var D → Fin (prefixGraph I B).size} (r : Recon I c D B sigma) (hM : r.Model) :
    ∃ s : Recon I c D B sigma, forall g, g < D.groups - 1 ->
      (s.exts g).length <= (B.word.length + 1) * (intervalAtom I c D g).observer.size := by
  have hall : forall g, ∃ t : IControl k × IControl k × List (Bool × Fin k), g < D.groups - 1 ->
      Gen I B (itemsAt I c D g) (sigma (zVar D g)).val t.1 t.2.2 (sigma (zVar D (g + 1))).val t.2.1 ∧
      t.1.state = markState D g ∧ t.1.next = nextOf D g ∧ t.1.seen = 0 ∧
      t.1.controls = (itemsAt I c D g).map (fun a => a.2.1) ∧
      t.2.1.state = markState D (g + 1) ∧ t.2.1.next = nextOf D (g + 1) ∧ t.2.1.seen = 1 ∧
      t.2.1.controls = (itemsAt I c D g).map (fun a => a.2.2) ∧
      t.2.2.length <= (B.word.length + 1) * (intervalAtom I c D g).observer.size := by
    intro g
    by_cases hg : g < D.groups - 1
    . obtain ⟨x0, x1, ext, hgen, h1, h2, h3, h4, h5, h6, h7, h8, hlen⟩ :=
        interval_trace_bounded I c D B (hM.atoms _ (mem_atoms_interval I c D hg))
      exact ⟨(x0, x1, ext), fun _ => ⟨hgen, h1, h2, h3, h4, h5, h6, h7, h8, hlen⟩⟩
    . exact ⟨(⟨markState D 0, none, 0, []⟩, ⟨markState D 0, none, 0, []⟩, []), fun h => absurd h hg⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hall
  let s : Recon I c D B sigma :=
    { r with exts := fun g => (f g).2.2, x0 := fun g => (f g).1, x1 := fun g => (f g).2.1,
             gen := fun g hg => (hf g hg).1,
             x0_state := fun g hg => (hf g hg).2.1,
             x0_next := fun g hg => (hf g hg).2.2.1,
             x0_seen := fun g hg => (hf g hg).2.2.2.1,
             x0_controls := fun g hg => (hf g hg).2.2.2.2.1,
             x1_state := fun g hg => (hf g hg).2.2.2.2.2.1,
             x1_next := fun g hg => (hf g hg).2.2.2.2.2.2.1,
             x1_seen := fun g hg => (hf g hg).2.2.2.2.2.2.2.1,
             x1_controls := fun g hg => (hf g hg).2.2.2.2.2.2.2.2.1 }
  exact ⟨s, fun g hg => (hf g hg).2.2.2.2.2.2.2.2.2⟩

theorem sum_map_mul_le {alpha : Type} (xs : List alpha) (f h : alpha -> Nat) (N : Nat)
    (hb : forall x, x ∈ xs -> f x <= N * h x) :
    (xs.map f).sum <= N * (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (fun y hy => hb y (by simp [hy]))
    simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using Nat.add_le_add hx ht

/-- Summing interval lengths counts each physical generator once. -/
theorem recon_length_le (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    {sigma : Var D → Fin (prefixGraph I B).size} (r : Recon I c D B sigma)
    (hr : forall g, g < D.groups - 1 -> (r.exts g).length <=
      (B.word.length + 1) * (intervalAtom I c D g).observer.size) :
    (extRef B r.ext).word.length + 1 <=
      (B.word.length + 1) * (clauseWeight (compileValid I c D) + 2) := by
  have hsum := sum_map_mul_le (List.range (D.groups - 1)) (fun g => (r.exts g).length)
    (fun g => (intervalAtom I c D g).observer.size) (B.word.length + 1)
    (fun g hg => hr g (List.mem_range.mp hg))
  have hweight : ((List.range (D.groups - 1)).map fun g =>
      (intervalAtom I c D g).observer.size).sum <= clauseWeight (compileValid I c D) := by
    unfold clauseWeight
    rw [RankQueryWeightBound.compile_sum]
    omega
  have hsum' := Nat.le_trans hsum (Nat.mul_le_mul_left (B.word.length + 1) hweight)
  rw [extRef_length]
  simp only [Recon.ext, List.length_cons, Recon.pre, List.length_flatMap] at *
  simp only [Nat.mul_add, Nat.mul_two]
  omega

/-- Concrete bounded reconstruction, stronger than semantic closure alone. -/
theorem compile_bounded (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    (hB : SafeReference I B) {P : Clause k} (hP : compileDiagram I c D = some P)
    (hsat : SatClause (prefixGraph I B) P) :
    ∃ C : Reference k, FirstReturnExt I B C ∧ SatClause (prefixGraph I C) c ∧
      C.word.length + 1 <= (B.word.length + 1) * (clauseWeight P + 2) := by
  unfold compileDiagram at hP
  split at hP
  . rename_i hv
    have hPe : P = compileValid I c D := (Option.some.inj hP).symm
    subst P
    obtain ⟨sigma, htests, hequal, hunequal, hatoms⟩ := hsat
    obtain ⟨r⟩ := exists_recon I c D B hv sigma htests hequal hatoms
    have hM : r.Model := ⟨htests, hequal, hunequal, hatoms⟩
    obtain ⟨s, hs⟩ := exists_bounded_recon I c D B r hM
    have hS : s.Model := ⟨htests, hequal, hunequal, hatoms⟩
    refine ⟨extRef B s.ext, s.firstReturnExt hB hv, ?_, recon_length_le I c D B s hs⟩
    refine ⟨fun v => s.assign v.val, ?_, ?_, ?_, ?_⟩
    . intro t ht
      exact s.test_sound hB hv hS (v := t.1) (t := t.2) ht
    . intro e he
      exact s.equal_sound hv hS (x := e.1) (y := e.2) he
    . intro e he
      exact s.unequal_sound hv hS (x := e.1) (y := e.2) he
    . intro a ha
      obtain ⟨ai, hai, rfl⟩ := List.mem_iff_getElem.mp ha
      exact s.atom_accepts hB hv hS hai
  . contradiction

/-- Every satisfied concrete preimage has a bounded common extension. -/
theorem preimage_bounded (I : Instance k) (phi : Query k) (B : Reference k)
    (hB : SafeReference I B) (hsat : Sat (prefixGraph I B) (preimage I RankQueryCoverage.budget phi)) :
    ∃ C : Reference k, FirstReturnExt I B C ∧ Sat (prefixGraph I C) phi ∧
      C.word.length + 1 <= (B.word.length + 1) *
        (RankQueryWeightBound.improvedBound k (weight phi) + 2) := by
  obtain ⟨P, hP, hsP⟩ := hsat
  have hw := RankQueryWeightBound.preimage_clause_weight_le I phi P hP
  obtain ⟨c, hc, hPc⟩ := List.mem_flatMap.mp hP
  obtain ⟨D, _, hD⟩ := (mem_preimageClause I c (RankQueryCoverage.budget c) P).mp hPc
  obtain ⟨C, hC, hsC, hlen⟩ := compile_bounded I c D B hB hD hsP
  exact ⟨C, hC, ⟨c, hc, hsC⟩, Nat.le_trans hlen
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 2))⟩

/-- Exact length strengthening of the existing finishing trace extraction. -/
theorem lengthRun_finish_trace (I : Instance k) (B : Reference k) (q0 : Fin k)
    {x y : Node (prefixGraph I B) (finishObserver I q0)} {n : Nat}
    (h : LengthRun (prefixGraph I B) (finishObserver I q0) x n y) :
    ∃ ext : List (Bool × Fin k),
      RankQueryFinishTrace.Trace I B x.1 x.2 ext y.1 y.2 ∧ ext.length = n := by
  induction h with
  | refl hx =>
    exact ⟨[], RankQueryFinishTrace.Trace.nil
      ((RankQueryFinishTrace.notEnd_iff I B _).mp
        ((RankQueryFinishFacts.finish_allowed_iff I q0 _ _).mp hx)), rfl⟩
  | @step n y z _ hs ih =>
    obtain ⟨ext, ht, hlen⟩ := ih
    obtain ⟨a, he, hi, hs, hb, hd, hm⟩ :=
      (RankQueryFinishTrace.prefix_step_iff I B q0 _ _ _ _).mp hs
    exact ⟨ext ++ ([(a, (show Fin k from z.2))] : List (Bool × Fin k)),
      RankQueryFinishTrace.Trace.snoc ht a he hi hs hb hd hm, by simp [hlen]⟩

/-- The final k-state observer yields a bounded ORIGINAL witness. -/
theorem finish_bounded (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    (h : Sat (prefixGraph I B) (finishQuery I)) :
    ∃ w : Word, Witness I w ∧ w.length + 1 <= (B.word.length + 1) * (k + 1) := by
  obtain ⟨v, hr⟩ := (RankQueryFinishTrace.sat_finish_iff_run I B).mp h
  have ha : Accepts (prefixGraph I B) (finishObserver I (B.label B.word.length))
      (RankQueryFinishTrace.parent B) v :=
    ⟨B.label B.word.length, List.mem_cons_self .., I.initial, List.mem_cons_self .., hr⟩
  obtain ⟨q, hq, p, hp, n, hn, hlen⟩ := accepts_length_bound _ _ ha
  have hq' : q = B.label B.word.length := List.mem_singleton.mp hq
  have hp' : p = I.initial := List.mem_singleton.mp hp
  subst q
  subst p
  obtain ⟨ext, ht, hext⟩ := lengthRun_finish_trace I B _ hn
  obtain ⟨hs, _, he⟩ := RankQueryFinishTrace.trace_safe_reference I B hB ht
  have hw := RankQueryFinishTrace.safe_reference_witness I (RankQueryFinishTrace.extend B ext) hs he
  refine ⟨(B.word ++ ext.map Prod.fst).reverse, ?_, ?_⟩
  . simpa only [RankQueryFinishTrace.extend_word] using hw
  . change n + 1 <= (B.word.length + 1) * k at hlen
    simp only [List.length_reverse, List.length_append, List.length_map, Nat.mul_add, Nat.mul_one]
    omega

/-- The product of the first h reconstruction factors, written recursively. -/
def growth (k : Nat) : Nat -> Nat
  | 0 => 1
  | h + 1 => (RankQueryWeightBound.weightBudget k (h + 1) + 2) * growth k h

theorem growth_step (k h : Nat) : growth k h <= growth k (h + 1) := by
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- Quantitative unwind for the ACTUAL finite preimage; no ClosureFor premise. -/
theorem promoted_finish_bounded (I : Instance k) : forall h (B : Reference k),
    SafeReference I B ->
    Sat (prefixGraph I B) (promote (preimage I RankQueryCoverage.budget) (finishQuery I) h) ->
    ∃ w : Word, Witness I w ∧
      w.length + 1 <= (B.word.length + 1) * (k + 1) * growth k h := by
  intro h
  induction h with
  | zero =>
    intro B hB hs
    simpa only [promote, growth, Nat.mul_one] using finish_bounded I B hB hs
  | succ h ih =>
    intro B hB hs
    rw [promote, RankQueryUnwind.sat_append] at hs
    rcases hs with hprev | hpre
    . obtain ⟨w, hw, hlen⟩ := ih B hB hprev
      exact ⟨w, hw, Nat.le_trans hlen (Nat.mul_le_mul_left _ (growth_step k h))⟩
    . obtain ⟨C, hC, hsat, hlen⟩ := preimage_bounded I _ B hB hpre
      have hweight := RankQueryWeightBound.improvedBound_mono k
        (RankQueryWeightBound.weight_promote_finish_le I h)
      have hCsize : C.word.length + 1 <= (B.word.length + 1) *
          (RankQueryWeightBound.weightBudget k (h + 1) + 2) :=
        Nat.le_trans hlen (Nat.mul_le_mul_left _ (Nat.add_le_add_right hweight 2))
      obtain ⟨w, hw, hwlen⟩ := ih C hC.safe hsat
      refine ⟨w, hw, Nat.le_trans hwlen ?_⟩
      calc
        (C.word.length + 1) * (k + 1) * growth k h <=
            ((B.word.length + 1) * (RankQueryWeightBound.weightBudget k (h + 1) + 2)) *
              (k + 1) * growth k h :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hCsize)
        _ = (B.word.length + 1) * (k + 1) * growth k (h + 1) := by
          rw [growth]
          ac_rfl

/-- Explicit total witness-length bound in the terminal automaton state count. -/
def witnessBound (k : Nat) : Nat :=
  if k = 1 then 0 else 2 * (k + 1) * growth k (k - 2)

/-- In a one-state terminal instance any original witness is empty. -/
theorem one_state_empty (I : Instance 1) (ht : TerminalRank.TerminalFinals I)
    {w : Word} (hw : Witness I w) : w = [] := by
  have hf := hw.2.1
  simp only [Subtail.stateAt, List.take_length] at hf
  cases hr : runFrom I I.initial w with
  | none => simp [hr, finalCheck] at hf
  | some f =>
    have hfin : I.final.get f = true := by simpa [hr, finalCheck] using hf
    have he : f = I.initial := Subsingleton.elim _ _
    subst f
    exact ((TerminalRank.runFrom_terminal I ht hfin w).mp hr).1

/-- Every positive terminal instance has an original witness below the new F.
The qualitative decision theorem is only used, never modified or strengthened
with a quantitative assumption. No arbitrary-tree subtype reduction is used. -/
theorem terminal_witness_bounded (I : Instance k) (ht : TerminalRank.TerminalFinals I)
    (h : ∃ w : Word, Witness I w) :
    ∃ w : Word, Witness I w ∧ w.length <= witnessBound k := by
  by_cases hk : k = 1
  . subst k
    obtain ⟨w, hw⟩ := h
    have he := one_state_empty I ht hw
    subst w
    exact ⟨[], hw, by simp [witnessBound]⟩
  . have hs := (RankQueryDecision.rankDecisionStatement I ht).mp h
    rcases hs with hempty | ⟨a, f, p, hB, hsat⟩
    . exact ⟨[], hempty, Nat.zero_le _⟩
    . obtain ⟨w, hw, hlen⟩ := promoted_finish_bounded I (k - 2) (oneLetter a f p) hB hsat
      have hn : (oneLetter a f p).word.length + 1 = 2 := rfl
      rw [hn] at hlen
      exact ⟨w, hw, by simp only [witnessBound, hk, if_false]; omega⟩

/-- The exact small-witness equivalence, with original Witness on both sides. -/
theorem terminal_witness_bound_iff (I : Instance k) (ht : TerminalRank.TerminalFinals I) :
    (∃ w : Word, Witness I w) <->
      ∃ w : Word, Witness I w ∧ w.length <= witnessBound k :=
  ⟨terminal_witness_bounded I ht, fun ⟨w, hw, _⟩ => ⟨w, hw⟩⟩

end Subtail.RankQueryLengthBound

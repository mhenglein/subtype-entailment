import Subtail.RankQueryLengthBound

/-!
F-only critical steps, 2026-09-20, base 19b06d4.
This additive module changes no core definition. It does not yet declare the
complete original-F theorem: the new finishing-query equivalence and milestone
composition are recorded in the ordinary proof for separate review.
-/
namespace Subtail.FOnlyAstra
open TerminalRank RankMilestones RankQuery RankQueryFinishTrace

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {k : Nat}

/-- Suffix cuts keep exactly the old labels after a return to the initial state. -/
theorem stateAt_drop_of_return (I : Instance k) (w : Word) (d i : Nat)
    (hr : stateAt I w d = some I.initial) :
    stateAt I (w.drop d) i = stateAt I w (d + i) := by
  rw [stateAt_add I w d i, hr]
  rfl

/-- Prefix deletion at an initial-state return creates no comparison seam. -/
theorem witness_drop_of_return (I : Instance k) {w : Word} (hw : Witness I w)
    {d : Nat} (hd : d <= w.length) (hr : stateAt I w d = some I.initial) :
    Witness I (w.drop d) := by
  refine ⟨?_, ?_, ?_⟩
  . intro i hi
    have hdi : d + i <= w.length := by simp only [List.length_drop] at hi; omega
    rw [stateAt_drop_of_return I w d i hr]
    exact hw.1 (d + i) hdi
  . have he : d + (w.drop d).length = w.length := by
      simp only [List.length_drop]
      omega
    rw [stateAt_drop_of_return I w d (w.drop d).length hr, he]
    exact hw.2.1
  . intro j hj i hij ha
    have hdj : d + j <= w.length := by simp only [List.length_drop] at hj; omega
    have hag : Agrees w (d + i) (d + j) := by
      simpa only [Agrees, List.drop_drop, Nat.add_comm] using ha
    rw [stateAt_drop_of_return I w d i hr, stateAt_drop_of_return I w d j hr]
    exact hw.2.2 (d + j) hdj (d + i) (by omega) hag

/-- Global shortestness implies the exact no-initial-return property used in F. -/
theorem shortest_no_initial_return (I : Instance k) {w : Word} (hw : Witness I w)
    (hmin : forall v : Word, Witness I v -> w.length <= v.length)
    {d : Nat} (hpos : 0 < d) (hd : d <= w.length) :
    stateAt I w d ≠ some I.initial := by
  intro hr
  have hs := witness_drop_of_return I hw hd hr
  have hm := hmin _ hs
  simp only [List.length_drop] at hm
  omega

private theorem nodup_map_on {alpha beta : Type} (g : alpha -> beta) (l : List alpha)
    (hn : l.Nodup)
    (hi : forall x, x ∈ l -> forall y, y ∈ l -> g x = g y -> x = y) :
    (l.map g).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.nodup_cons]
    constructor
    . intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have hba := hi b (by simp [hb]) a (by simp) he
      exact ha (hba ▸ hb)
    . exact ih hl (fun x hx y hy h => hi x (by simp [hx]) y (by simp [hy]) h)

/-- Excluding the original initial state leaves at most k-1 distinct borders,
INCLUDING the empty border. This is the extra unit absent from the old rank cap. -/
theorem border_count_add_one_le_of_avoids (I : Instance k)
    (ht : TerminalFinals I) {q f : Fin k} {u : Word}
    (hu : runFrom I q u = some f) (hf : I.final.get f = true)
    (havoid : forall i, i <= u.length -> cutState I q u i ≠ I.initial) :
    (borderLengths u).length + 1 <= k := by
  have hn : ((borderLengths u).map (borderState I q u)).Nodup := by
    apply nodup_map_on _ _ (borders_nodup u)
    intro x hx y hy he
    exact borderState_injective I ht hu hf hx hy he
  have hnot : I.initial ∉ (borderLengths u).map (borderState I q u) := by
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact havoid (u.length - b) (Nat.sub_le _ _) he
  have hc := List.nodup_cons.mpr (And.intro hnot hn)
  have hle := hc.length_le_of_subset (l₂ := List.finRange k)
    (fun x _ => List.mem_finRange x)
  simpa using hle

/-- The proper-suffix positive-border rank is at most k-2. -/
theorem rank_le_of_avoids (I : Instance k)
    (ht : TerminalFinals I) {q f : Fin k} {u : Word}
    (hu : runFrom I q u = some f) (hf : I.final.get f = true)
    (havoid : forall i, i <= u.length -> cutState I q u i ≠ I.initial) :
    rank u <= k - 2 := by
  have h := border_count_add_one_le_of_avoids I ht hu hf havoid
  have hp := borders_length_pos u
  simp only [rank, positiveBorderCount]
  omega

/-- A fresh final return is safe using the OLD full-reference mask. This differs
from the existing no-return trace only at the target of its last step. -/
theorem final_return_safe (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    {ext : List (Prod Bool (Fin k))} {v : Pos B} {q : Fin k}
    (ht : Trace I B (parent B) (B.label B.word.length) ext v q)
    (a : Bool) (r : Fin k)
    (ha : RankQuery.advance B.word v.val a = B.word.length)
    (hs : step I r a = some q) (hb : I.bad.get r = false)
    (hd : (I.flags.get r).get r = false)
    (hm : (mask I B B.word.length).get r = false) :
    SafeReference I (appendLetter (extend B ext) a r) := by
  obtain ⟨hC, hparent, hlabel⟩ := trace_safe_reference I B hB ht
  let C := extend B ext
  let D := appendLetter C a r
  have hBC : Extends B C := extend_extends B ext
  have hv : v.val < B.word.length := (notEnd_iff I B v).mp
    ((RankQueryFinishFacts.finish_run_notEnd I (B.label B.word.length)
      (trace_run I B _ ht)).2)
  have hpar : failureParent D.word = B.word.length :=
    (append_parent hBC hC.nonempty hparent hv a r).trans ha
  have hBD := hBC.trans (appendLetter_extends C a r)
  have hnewlabel : D.label D.word.length = r := by
    change (if (C.word ++ [a]).length <= C.word.length then C.label (C.word ++ [a]).length else r) = r
    rw [if_neg (by simp)]
  have hmask : (mask I D D.word.length).get r = false := by
    rw [RankQueryFirstReturn.mask_get_eq]
    rw [FirstReturnGraph.mask_decomposition (Nat.le_refl _) (by simp [D, appendLetter])]
    rw [List.take_length, hpar, hnewlabel]
    rw [← RankQueryFirstReturn.mask_get_eq, extends_mask hBD I (Nat.le_refl _)]
    rw [hd, hm]
    rfl
  exact safe_appendLetter I C a r hC (by rwa [hlabel]) hb hmask

/-- With the last control initial, the same final step yields ORIGINAL Witness. -/
theorem final_return_witness (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    {ext : List (Prod Bool (Fin k))} {v : Pos B} {q : Fin k}
    (ht : Trace I B (parent B) (B.label B.word.length) ext v q) (a : Bool)
    (ha : RankQuery.advance B.word v.val a = B.word.length)
    (hs : step I I.initial a = some q) (hb : I.bad.get I.initial = false)
    (hd : (I.flags.get I.initial).get I.initial = false)
    (hm : (mask I B B.word.length).get I.initial = false) :
    Witness I (appendLetter (extend B ext) a I.initial).word.reverse := by
  apply safe_reference_witness I _ (final_return_safe I B hB ht a I.initial ha hs hb hd hm)
  change (if ((extend B ext).word ++ [a]).length <= (extend B ext).word.length
    then (extend B ext).label ((extend B ext).word ++ [a]).length else I.initial) = I.initial
  rw [if_neg (by simp)]

/-- A finite k-control observer: end may be visited ONLY as an accepting final
control and has no outgoing moves. It is a new query, not a compiler mutation. -/
def finishPlusObserver (I : Instance k) (q : Fin k) : Observer k where
  size := k
  initial := [q]
  final := [I.initial]
  allows := fun p c => !c.isEnd || decide (p = I.initial)
  move := fun q c l d =>
    if c.isEnd then [] else
      match l with
      | .K a => (List.finRange k).filter fun p =>
          step I p a == some q && !I.bad.get p && !(I.flags.get p).get p &&
          !d.mask.get p && (!d.isEnd || decide (p = I.initial))
      | _ => []

def finishPlusQuery (I : Instance k) : Query k :=
  (List.finRange k).map fun q =>
    { vars := 3
      tests := [(0, fun c => c.isEnd && decide (c.state = q))]
      equal := []
      unequal := []
      atoms := [⟨oneEdge .F, 0, 1⟩, ⟨finishPlusObserver I q, 1, 2⟩] }

theorem weight_finishPlus_le (I : Instance k) : weight (finishPlusQuery I) <= k + 10 := by
  unfold weight
  apply RankQueryUnwind.maxNat_le_of_forall
  intro n hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  unfold finishPlusQuery at hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
  simp [clauseWeight, sumSizes, oneEdge, finishPlusObserver]
  omega

/-- Elementary one-stage lag. No compiler-size assumption is hidden here. -/
theorem lag_step (a x y : Nat) (hx : 3 <= x) (ha1 : 1 <= a)
    (ha : a <= x ^ 4) (hxy : 6 * x ^ 2 <= y) :
    6 * (a * x ^ (6 * x ^ 2 + 2)) ^ 2 <= a * y ^ (2 * y + 2) := by
  have hxpos : 0 < x := by omega
  have h6 : 6 <= x ^ 2 := by
    have hh := Nat.pow_le_pow_left hx 2
    simp at hh
    omega
  have ha2 : a ^ 2 <= x ^ 8 := by
    have hh := Nat.pow_le_pow_left ha 2
    simpa [← Nat.pow_mul] using hh
  have he : (6 * x ^ 2 + 2) * 2 = 12 * x ^ 2 + 4 := by omega
  have hcoef : 6 * a ^ 2 <= x ^ 10 := by
    have hh := Nat.mul_le_mul h6 ha2
    simpa [← Nat.pow_add] using hh
  have hexp : 12 * x ^ 2 + 14 <= 4 * y + 4 := by
    omega
  have hbase : x ^ 2 <= y := by omega
  calc
    6 * (a * x ^ (6 * x ^ 2 + 2)) ^ 2
        = (6 * a ^ 2) * x ^ (12 * x ^ 2 + 4) := by
            rw [Nat.mul_pow, ← Nat.pow_mul, he]
            ac_rfl
    _ <= x ^ 10 * x ^ (12 * x ^ 2 + 4) := Nat.mul_le_mul_right _ hcoef
    _ = x ^ (12 * x ^ 2 + 14) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    _ <= x ^ (4 * y + 4) := Nat.pow_le_pow_right hxpos hexp
    _ = (x ^ 2) ^ (2 * y + 2) := by
      rw [← Nat.pow_mul]
      congr 1
      omega
    _ <= y ^ (2 * y + 2) := Nat.pow_le_pow_left hbase _
    _ <= a * y ^ (2 * y + 2) := Nat.le_mul_of_pos_left _ (by omega)

/-- The coefficient condition persists throughout the corrected recurrence. -/
theorem coefficient_le_fourth (k x : Nat) (hx : k + 10 <= x) : 64 * k <= x ^ 4 := by
  have hk : k <= x := by omega
  have hp : 64 <= x ^ 3 := by
    have hh := Nat.pow_le_pow_left (show 4 <= x by omega) 3
    simp at hh
    exact hh
  have h := Nat.mul_le_mul hp hk
  simpa [Nat.pow_succ] using h

theorem corrected_budget_ge_seed (k : Nat) (hk : 0 < k) :
    forall j, k + 10 <= RankQueryWeightBound.weightBudget k j := by
  intro j
  induction j with
  | zero => simp [RankQueryWeightBound.weightBudget]
  | succ j ih =>
    exact Nat.le_trans ih (RankQueryWeightBound.le_improvedBound k _ hk (by omega))

/-- The corrected j-th budget fits under the original (j+1)-st budget. -/
theorem budgets_lag (k : Nat) (hk : 0 < k) : forall j,
    6 * (RankQueryWeightBound.weightBudget k j) ^ 2 <=
      RankQueryUnwind.weightBudget k (j + 1) := by
  intro j
  induction j with
  | zero =>
    change 6 * (k + 10) ^ 2 <= 64 * k * (k + 10) ^ (2 * (k + 10) + 2)
    exact Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega))
  | succ j ih =>
    have hx := corrected_budget_ge_seed k hk j
    have h := lag_step (64 * k) (RankQueryWeightBound.weightBudget k j)
      (RankQueryUnwind.weightBudget k (j + 1)) (by omega) (by omega)
      (coefficient_le_fourth k _ hx) ih
    exact h


/-- Exact old recurrence product; no change to the repository's old U. -/
def oldGrowth (k : Nat) : Nat -> Nat
  | 0 => 1
  | h + 1 => (RankQueryUnwind.weightBudget k (h + 1) + 2) * oldGrowth k h

/-- Original C080 F for k>=1. The totalization at 0 has no input instances. -/
def originalF (k : Nat) : Nat :=
  if k = 1 then 0 else 2 * (k + 1) * oldGrowth k (k - 2)

theorem budget_le_next (k : Nat) (hk : 0 < k) (j : Nat) :
    RankQueryWeightBound.weightBudget k j <= RankQueryUnwind.weightBudget k (j + 1) := by
  have hx := corrected_budget_ge_seed k hk j
  have hp : RankQueryWeightBound.weightBudget k j <=
      (RankQueryWeightBound.weightBudget k j) ^ 2 := by
    calc
      _ = (RankQueryWeightBound.weightBudget k j) ^ 1 := by simp
      _ <= _ := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.le_trans hp (Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 6))
    (budgets_lag k hk j))

/-- Saving one promotion absorbs the larger corrected recurrence. -/
theorem growth_lag (k : Nat) (hk : 0 < k) : forall h,
    RankQueryLengthBound.growth k h <= oldGrowth k (h + 1) := by
  intro h
  induction h with
  | zero => simp [RankQueryLengthBound.growth, oldGrowth]
  | succ h ih =>
    change (RankQueryWeightBound.weightBudget k (h + 1) + 2) *
      RankQueryLengthBound.growth k h <=
      (RankQueryUnwind.weightBudget k ((h + 1) + 1) + 2) * oldGrowth k (h + 1)
    exact Nat.mul_le_mul (Nat.add_le_add_right (budget_le_next k hk (h + 1)) 2) ih

theorem one_less_product_le_originalF (k : Nat) (hk : 3 <= k) :
    2 * (k + 1) * RankQueryLengthBound.growth k (k - 3) <= originalF k := by
  have h := growth_lag k (by omega) (k - 3)
  have he : k - 3 + 1 = k - 2 := by omega
  rw [he] at h
  unfold originalF
  rw [if_neg (by omega)]
  exact Nat.mul_le_mul_left (2 * (k + 1)) h

/-- All small-state instances satisfy exact original F, using existing C082. -/
theorem original_F_small (I : Instance k) (hk : k <= 2) (ht : TerminalFinals I) :
    (Exists fun w : Word => Witness I w) <->
      (Exists fun w : Word => Witness I w ∧ w.length <= originalF k) := by
  by_cases h0 : k = 0
  . subst k
    exact Fin.elim0 I.initial
  . by_cases h1 : k = 1
    . subst k
      simpa [originalF, RankQueryLengthBound.witnessBound] using
        RankQueryLengthBound.terminal_witness_bound_iff I ht
    . have h2 : k = 2 := by omega
      subst k
      simpa [originalF, oldGrowth, RankQueryLengthBound.witnessBound,
        RankQueryLengthBound.growth] using RankQueryLengthBound.terminal_witness_bound_iff I ht

#guard originalF 1 = 0
#guard originalF 2 = 6

private def unaryThree : Instance 3 where
  initial := 0
  transitions := #v[(some 1, none), (some 2, none), (none, none)]
  bad := #v[false, false, false]
  final := #v[false, false, true]
  flags := #v[#v[false, false, false], #v[false, false, false], #v[false, false, false]]

private def unaryBase : Reference 3 where
  word := [false]
  label := fun j => if j = 0 then 2 else 1

#guard witnessCheck unaryThree [false, false] = true
#guard satCheck (prefixGraph unaryThree unaryBase) (finishQuery unaryThree) = false
#guard satCheck (prefixGraph unaryThree unaryBase) (finishPlusQuery unaryThree) = true

#print axioms stateAt_drop_of_return
#print axioms witness_drop_of_return
#print axioms shortest_no_initial_return
#print axioms border_count_add_one_le_of_avoids
#print axioms rank_le_of_avoids
#print axioms final_return_safe
#print axioms final_return_witness
#print axioms finishPlusObserver
#print axioms finishPlusQuery
#print axioms weight_finishPlus_le
#print axioms lag_step
#print axioms coefficient_le_fourth
#print axioms corrected_budget_ge_seed
#print axioms budgets_lag
#print axioms oldGrowth
#print axioms originalF
#print axioms budget_le_next
#print axioms growth_lag
#print axioms one_less_product_le_originalF
#print axioms original_F_small
end Subtail.FOnlyAstra

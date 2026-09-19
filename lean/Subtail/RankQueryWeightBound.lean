import Subtail.RankQueryCoverage
import Subtail.RankQueryUnwind

/-!
# A sufficient size bound for the unchanged concrete compiler

C080 / A017-A018, issue #30. This is a separate quantitative theorem, not a
change to closureBound, ClosureFor, the enumerator or the terminal decider.
The argument counts the whole syntactic envelope, not only normal-form paths.
-/
namespace Subtail.RankQueryWeightBound
open RankQuery RankQueryCompiler RankQueryEnumeration

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {k : Nat}

/-- Observer sizes are counted per atom occurrence, exactly as in clauseWeight. -/
def atomSum (xs : List (Atom k v)) : Nat := (xs.map fun a => a.observer.size).sum

/-- The observations of one physical interval, preserving repetitions. -/
def selected (g : Nat) (e : Emitted D) : List (Active k) :=
  (e.active.filter fun x => x.1 = g).map fun x => x.2

/-- An additive per-piece estimate, simultaneously for atoms and observations. -/
structure Estimate (T g n : Nat) (e : Emitted D) : Prop where
  atoms : e.atoms.length ≤ n
  sizes : atomSum e.atoms ≤ n * T
  active : (selected g e).length ≤ n
  activeSizes : ∀ x ∈ selected g e, x.1.size ≤ T

theorem selected_append (g : Nat) (e f : Emitted D) :
    selected g (appendEmitted e f) = selected g e ++ selected g f := by
  simp [selected, appendEmitted, List.filter_append, List.map_append]

theorem estimate_blank (ts : List (Var D × (Colour k → Bool)))
    (eqs : List (Var D × Var D)) (n : Nat) :
    Estimate T g n ({ tests := ts, equal := eqs } : Emitted D) := by
  constructor <;> simp [selected, atomSum]

theorem estimate_mono {e : Emitted D} (h : Estimate T g m e) (hm : m ≤ n) :
    Estimate T g n e :=
  ⟨Nat.le_trans h.atoms hm, Nat.le_trans h.sizes (Nat.mul_le_mul_right T hm),
    Nat.le_trans h.active hm, h.activeSizes⟩

theorem estimate_append {e f : Emitted D}
    (he : Estimate T g m e) (hf : Estimate T g n f) :
    Estimate T g (m + n) (appendEmitted e f) := by
  constructor
  · simpa [appendEmitted] using Nat.add_le_add he.atoms hf.atoms
  · simpa [appendEmitted, atomSum, List.map_append, List.sum_append, Nat.add_mul]
      using Nat.add_le_add he.sizes hf.sizes
  · simpa [selected_append] using Nat.add_le_add he.active hf.active
  · intro x hx
    rw [selected_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact he.activeSizes x hx
    · exact hf.activeSizes x hx

/-- An injective interval index contributes at most one observation per piece. -/
theorem filter_add_length_le_one (n i g : Nat) (f : Nat → α) :
    (((List.range n).map fun t => (i + t, f t)).filter fun x => x.1 = g).length ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append]
    by_cases h : i + n = g
    · have hnil : (((List.range n).map fun t => (i + t, f t)).filter fun x => x.1 = g) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        have ht' := List.mem_range.mp ht
        simp only [decide_eq_false_iff_not]
        omega
      simp [hnil, h]
    · simpa [h] using ih

theorem forward_selected_length (D : Diagram k) (ai pi i j : Nat) (o : Observer k) (P : Piece) :
    (selected g ({ active := forwardActive D ai pi i j o P } : Emitted D)).length ≤ 1 := by
  unfold selected forwardActive
  simp only [List.length_map]
  exact filter_add_length_le_one _ _ _ _

theorem forward_selected_observer (D : Diagram k) (ai pi i j : Nat) (o : Observer k) (P : Piece)
    {x : Active k} (hx : x ∈ selected g ({ active := forwardActive D ai pi i j o P } : Emitted D)) :
    x.1 = o := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy, _⟩ := List.mem_filter.mp hy
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hy
  rfl

/-- This estimate needs no validity or product-simplicity hypothesis. -/
theorem compilePiece_estimate (I : Instance k) (D : Diagram k) (ai pi : Nat)
    (o : Observer k) (P : Piece) (hT : 2 ≤ T) (ho : o.size ≤ T) (g : Nat) :
    Estimate T g 1 (compilePiece I D ai pi o P) := by
  unfold compilePiece
  cases hl : finOf o.size P.lc with
  | none => exact estimate_blank [] [] 1
  | some lc =>
    cases hr : finOf o.size P.rc with
    | none => exact estimate_blank [] [] 1
    | some rc =>
      cases hk : P.kind with
      | core =>
        constructor
        · simp
        · simpa [atomSum, coreObs, sliceObs] using ho
        · simp [selected]
        · simp [selected]
      | forward =>
        split
        · exact estimate_blank _ [] 1
        · constructor
          · simp
          · simp [atomSum]
          · exact forward_selected_length D ai pi P.source P.target o P
          · intro x hx
            rw [forward_selected_observer D ai pi P.source P.target o P hx]
            exact ho
      | enter => exact estimate_blank _ _ 1
      | wrap => exact estimate_blank _ [] 1
      | exit =>
        cases he : P.label with
        | F => exact estimate_blank _ _ 1
        | S => exact estimate_blank [] [] 1
        | K b =>
          constructor
          · simp
          · simpa [atomSum, edgeObs] using hT
          · simp [selected]
          · simp [selected]

theorem estimate_fold_aux (xs : List (Emitted D)) (N : Nat)
    (hx : ∀ x ∈ xs, Estimate T g N x) (e : Emitted D) (m : Nat) (he : Estimate T g m e) :
    Estimate T g (m + xs.length * N) (xs.foldl appendEmitted e) := by
  induction xs generalizing e m with
  | nil => simpa using he
  | cons x xs ih =>
    have hfirst := hx x (by simp)
    have htail := ih (fun y hy => hx y (by simp [hy]))
      (appendEmitted e x) (m + N) (estimate_append he hfirst)
    simpa [List.foldl_cons, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem estimate_fold (xs : List (Emitted D)) (N : Nat)
    (hx : ∀ x ∈ xs, Estimate T g N x) :
    Estimate T g (xs.length * N) (xs.foldl appendEmitted {}) := by
  simpa using estimate_fold_aux xs N hx {} 0 (estimate_blank [] [] 0)

theorem compileAtom_estimate (I : Instance k) (D : Diagram k) (ai : Nat)
    (o : Observer k) (ps : List Piece) (hT : 2 ≤ T) (ho : o.size ≤ T) (g : Nat) :
    Estimate T g ps.length (compileAtom I D ai o ps) := by
  unfold compileAtom
  have h := estimate_fold
    ((List.range ps.length).map fun pi => compilePiece I D ai pi o (ps.getD pi default)) 1
    (by
      intro e he
      obtain ⟨pi, _, rfl⟩ := List.mem_map.mp he
      exact compilePiece_estimate I D ai pi o _ hT ho g)
  simpa using h

theorem piecesOf_length_le (D : Diagram k) (P : Nat)
    (hp : ∀ ps ∈ D.pieces, ps.length ≤ P) (ai : Nat) : (piecesOf D ai).length ≤ P := by
  unfold piecesOf
  rw [List.getD_eq_getElem?_getD]
  cases h : D.pieces[ai]? with
  | none => simp
  | some ps => exact hp ps (List.mem_of_getElem? h)

theorem allEmitted_estimate (I : Instance k) (c : Clause k) (D : Diagram k)
    (P T : Nat) (hT : 2 ≤ T) (ho : ∀ a ∈ c.atoms, a.observer.size ≤ T)
    (hp : ∀ ps ∈ D.pieces, ps.length ≤ P) (g : Nat) :
    Estimate T g (c.atoms.length * P) (allEmitted I c D) := by
  unfold allEmitted
  have h := estimate_fold
    ((List.range c.atoms.length).map fun ai =>
      match c.atoms[ai]? with
      | some atm => compileAtom I D ai atm.observer (piecesOf D ai)
      | none => ({} : Emitted D)) P
    (by
      intro e he
      obtain ⟨ai, _, rfl⟩ := List.mem_map.mp he
      cases ha : c.atoms[ai]? with
      | none => exact estimate_blank [] [] P
      | some atm =>
        exact estimate_mono
          (compileAtom_estimate I D ai atm.observer (piecesOf D ai)
            hT (ho atm (List.mem_of_getElem? ha)) g)
          (piecesOf_length_le D P hp ai))
  simpa using h

theorem prod_sizes_le (xs : List (Active k)) (h : ∀ x ∈ xs, x.1.size ≤ T) :
    prodList (xs.map fun x => x.1.size) ≤ T ^ xs.length := by
  induction xs with
  | nil => simp [prodList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simpa [prodList, Nat.pow_succ, Nat.mul_comm] using Nat.mul_le_mul hx hxs

theorem interval_cardinality (I : Instance k) (c : Clause k) (D : Diagram k) (g : Nat) :
    (intervalAtom I c D g).observer.size =
      6 * k * prodList ((itemsAt I c D g).map fun x => x.1.size) := by
  simp [intervalAtom, intervalObs, intervalSize, intervalSizes, prodList,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem interval_size_le (I : Instance k) (c : Clause k) (D : Diagram k)
    (hT : 2 ≤ T) (h : Estimate T g N (allEmitted I c D)) :
    (intervalAtom I c D g).observer.size ≤ 6 * k * T ^ N := by
  rw [interval_cardinality]
  apply Nat.mul_le_mul_left
  have hp := prod_sizes_le (selected g (allEmitted I c D)) h.activeSizes
  exact Nat.le_trans hp (Nat.pow_le_pow_right (by omega : 0 < T) h.active)

/-- The coverage module's indexed sum is the same sum used by clauseWeight. -/
theorem coverage_sum_eq (c : Clause k) : RankQueryCoverage.sumSizes c = RankQuery.sumSizes c := by
  unfold RankQueryCoverage.sumSizes RankQuery.sumSizes
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hil : i < c.atoms.length := by simpa using hi
    simp [RankQueryCoverage.obsAt, List.getElem?_eq_getElem hil]

theorem member_le_sum {n : Nat} {xs : List Nat} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp only [List.sum_cons]
      omega

theorem compile_atoms_length (I : Instance k) (c : Clause k) (D : Diagram k) :
    (compileValid I c D).atoms.length = 2 + (allEmitted I c D).atoms.length + (D.groups - 1) := by
  simp [compileValid, baseAtoms]

theorem compile_sum (I : Instance k) (c : Clause k) (D : Diagram k) :
    RankQuery.sumSizes (compileValid I c D) = 4 + atomSum (allEmitted I c D).atoms +
      ((List.range (D.groups - 1)).map fun g => (intervalAtom I c D g).observer.size).sum := by
  simp [compileValid, baseAtoms, RankQuery.sumSizes, atomSum, oneEdge, edgeObs,
    List.map_append, List.sum_append, List.map_map, Function.comp_def, Nat.add_assoc]

/-- A conservative sufficient replacement for the oversized syntactic envelope. -/
def improvedBound (k T : Nat) : Nat := 64 * k * T ^ (6 * T ^ 2 + 2)

theorem compileValid_weight_le (I : Instance k) (c : Clause k) (D : Diagram k)
    (hb : Bounded c (RankQueryCoverage.budget c) D) :
    clauseWeight (compileValid I c D) ≤ improvedBound k (clauseWeight c) := by
  let T := clauseWeight c
  let P := 2 * RankQueryCoverage.blockBound c
  let M := c.atoms.length * P
  have hT : 2 ≤ T := Nat.le_max_left _ _
  have hsum : 1 + c.vars + c.atoms.length + RankQuery.sumSizes c ≤ T := Nat.le_max_right _ _
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le I.initial.val) I.initial.isLt
  have hP : P ≤ 6 * T := by
    dsimp [P, RankQueryCoverage.blockBound]
    rw [coverage_sum_eq]
    omega
  have hM : M ≤ 6 * T ^ 2 := by
    calc
      M = c.atoms.length * P := rfl
      _ ≤ T * (6 * T) := Nat.mul_le_mul (by omega) hP
      _ = 6 * T ^ 2 := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hG : RankQueryCoverage.groupBound c ≤ 2 * T := by
    unfold RankQueryCoverage.groupBound
    rw [coverage_sum_eq]
    omega
  obtain ⟨_, hng, hnc, _, _, _, _, _, hpieces, _, _⟩ := hb
  have hn : D.groups ≤ 2 * T := Nat.le_trans hng hG
  have hcore : D.coreVars ≤ c.vars + M := by
    simpa [RankQueryCoverage.budget, RankQueryCoverage.coreBound, M, P,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnc
  have hp : ∀ ps ∈ D.pieces, ps.length ≤ P := fun ps hps => (hpieces ps hps).1
  have ho : ∀ a ∈ c.atoms, a.observer.size ≤ T := by
    intro a ha
    have hs : a.observer.size ≤ RankQuery.sumSizes c :=
      member_le_sum (List.mem_map.mpr ⟨a, ha, rfl⟩)
    omega
  have hem (g : Nat) : Estimate T g M (allEmitted I c D) :=
    allEmitted_estimate I c D P T hT ho hp g
  have hint (g : Nat) : (intervalAtom I c D g).observer.size ≤ 6 * k * T ^ (6 * T ^ 2) :=
    interval_size_le I c D hT (estimate_mono (hem g) hM)
  have hinterval : ((List.range (D.groups - 1)).map fun g =>
      (intervalAtom I c D g).observer.size).sum ≤ 12 * k * T ^ (6 * T ^ 2 + 1) := by
    calc
      _ ≤ (List.range (D.groups - 1)).length * (6 * k * T ^ (6 * T ^ 2)) :=
        RankQueryCoverage.sum_map_le_const (fun g _ => hint g)
      _ ≤ (2 * T) * (6 * k * T ^ (6 * T ^ 2)) :=
        Nat.mul_le_mul_right _ (by simp; omega)
      _ = 12 * k * T ^ (6 * T ^ 2 + 1) := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hMT : M * T ≤ 6 * T ^ 3 := by
    calc
      M * T ≤ (6 * T ^ 2) * T := Nat.mul_le_mul_right T hM
      _ = 6 * T ^ 3 := by simp [Nat.pow_succ, Nat.mul_assoc]
  have hvars : (compileValid I c D).vars ≤ 2 + 3 * T + M := by
    change 2 + D.groups + D.coreVars ≤ _
    omega
  have hatoms : (compileValid I c D).atoms.length ≤ 2 + M + 2 * T := by
    rw [compile_atoms_length]
    have := (hem 0).atoms
    omega
  have hsizes : RankQuery.sumSizes (compileValid I c D) ≤
      4 + 6 * T ^ 3 + 12 * k * T ^ (6 * T ^ 2 + 1) := by
    rw [compile_sum]
    have := (hem 0).sizes
    omega
  have hpoly : 9 + 5 * T + 12 * T ^ 2 + 6 * T ^ 3 ≤ 32 * T ^ 3 := by
    have h1 : 1 ≤ T ^ 3 := Nat.pow_pos (by omega)
    have ht : T ≤ T ^ 3 := by
      calc
        T = T ^ 1 := by simp
        _ ≤ T ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
    have ht2 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hpow : T ^ 3 ≤ T ^ (6 * T ^ 2 + 2) := by
    have ht2 : 0 < T ^ 2 := Nat.pow_pos (by omega)
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hkp : T ^ (6 * T ^ 2 + 2) ≤ k * T ^ (6 * T ^ 2 + 2) :=
    Nat.le_mul_of_pos_left _ hk
  have hmain : 32 * T ^ 3 ≤ 32 * k * T ^ (6 * T ^ 2 + 2) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 32 (Nat.le_trans hpow hkp)
  have hlast : 12 * k * T ^ (6 * T ^ 2 + 1) ≤ 12 * k * T ^ (6 * T ^ 2 + 2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hraw : 1 + (compileValid I c D).vars + (compileValid I c D).atoms.length +
      RankQuery.sumSizes (compileValid I c D) ≤
      32 * k * T ^ (6 * T ^ 2 + 2) + 12 * k * T ^ (6 * T ^ 2 + 2) := by
    omega
  have hpos : 0 < k * T ^ (6 * T ^ 2 + 2) := Nat.mul_pos hk (Nat.pow_pos (by omega))
  change max 2 (1 + (compileValid I c D).vars + (compileValid I c D).atoms.length +
    RankQuery.sumSizes (compileValid I c D)) ≤ 64 * k * T ^ (6 * T ^ 2 + 2)
  simp only [Nat.mul_assoc] at hraw ⊢
  omega

end Subtail.RankQueryWeightBound

import Subtail.RankQueryWeightBound
import Subtail.RankQueryWeightCounterexample

/-!
# A smaller existential first-return compiler (#69, compiler-only)

Keep the old enumeration and compiler untouched. Reject a diagram only when
some physical interval has more than a + S active coordinates. The coverage
construction already has at most 1 + size fresh blocks per atom on ONE fixed
extension. A shared interval retains every surviving coordinate, including
repetitions, so its reconstruction continues to use one generated word.

This module makes no original-F or shortest-witness claim.
-/
namespace Subtail.SmallerCompilerAstra
open RankQuery RankQueryCompiler RankQueryEnumeration RankQueryWeightBound

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

variable {k : Nat}

def activeBudget (c : Clause k) : Nat :=
  c.atoms.length + RankQueryCoverage.sumSizes c

/-- Check the coordinate budget before constructing any interval observer. -/
def compact (I : Instance k) (c : Clause k) (D : Diagram k) : Bool :=
  (List.range (D.groups - 1)).all fun g =>
    decide ((itemsAt I c D g).length <= activeBudget c)

theorem compact_iff (I : Instance k) (c : Clause k) (D : Diagram k) :
    compact I c D = true <->
      forall g, g < D.groups - 1 -> (itemsAt I c D g).length <= activeBudget c := by
  simp [compact, List.all_eq_true, List.mem_range]

/-- No reference, graph, generated word, or semantic test enters this filter. -/
def smallDiagrams (I : Instance k) (c : Clause k) : List (Diagram k) :=
  (diagrams c (RankQueryCoverage.budget c)).filter (compact I c)

def preClause (I : Instance k) (c : Clause k) : Query k :=
  preimageOver I c (smallDiagrams I c)

def preSmall (I : Instance k) (phi : Query k) : Query k :=
  phi.flatMap (preClause I)

theorem mem_preClause (I : Instance k) (c out : Clause k) :
    out ∈ preClause I c <->
      exists D, Bounded c (RankQueryCoverage.budget c) D ∧
        compact I c D = true ∧ compileDiagram I c D = some out := by
  simp [preClause, preimageOver, smallDiagrams, List.mem_filterMap,
    List.mem_filter, mem_diagrams, and_assoc]

/-! ## The existing coverage diagram survives the guard -/

section CoverageCount
open RankQueryCoverage RankQueryPaths

/-- Indexing a finite list does not change multiplicity, even with duplicates. -/
theorem map_range_getD {alpha : Type} [Inhabited alpha] (xs : List alpha) :
    (List.range xs.length).map (fun j => xs.getD j default) = xs := by
  apply List.ext_getElem
  . simp
  . intro j hj hx
    simp [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hx]

theorem filter_indices_length {alpha : Type} [Inhabited alpha]
    (xs : List alpha) (p : alpha -> Bool) :
    ((List.range xs.length).filter fun j => p (xs.getD j default)).length =
      (xs.filter p).length := by
  have h := congrArg (fun ys : List alpha => (ys.filter p).length) (map_range_getD xs)
  simpa [List.filter_map, List.length_map] using h

/-- Inject contributing piece indices into fresh block indices. Portal pieces
never contribute; distinct occurrences are NOT identified with each other. -/
theorem covered_count_le {I : Instance k} {B : Reference k} {E : Ext I B}
    {c : Clause k} (X : Cov I B E c) (ai : Nat) (hai : ai < c.atoms.length) (g : Nat) :
    ((List.range (X.pieces ai).length).filter fun pi => X.coversPi ai pi g).length <=
      freshCount B.word.length (X.segs ai) := by
  let chosen := (List.range (X.pieces ai).length).filter fun pi => X.coversPi ai pi g
  let freshIndices := (List.range (X.segCount ai)).filter fun si =>
    isFresh B.word.length (X.blk ai si)
  have hn : chosen.Nodup := List.Pairwise.filter _ List.nodup_range
  have hs : forall pi, pi ∈ chosen -> pi ∈ (freshIndices.map fun si => 2 * si) := by
    intro pi hp
    obtain ⟨hr, hc⟩ := List.mem_filter.mp hp
    obtain ⟨si, heq, hsi, hf, _, _⟩ := X.coversPi_block hai (List.mem_range.mp hr) hc
    subst pi
    exact List.mem_map.mpr ⟨si, List.mem_filter.mpr ⟨List.mem_range.mpr hsi, hf⟩, rfl⟩
  have h := hn.length_le_of_subset hs
  rw [List.length_map] at h
  have he : freshIndices.length = freshCount B.word.length (X.segs ai) := by
    simpa [freshIndices, Cov.segCount, Cov.blk, freshCount] using
      filter_indices_length (X.segs ai) (isFresh B.word.length)
  exact Nat.le_trans h (Nat.le_of_eq he)

/-- Per-atom product-simple paths were chosen inside the SAME C. Their fresh
block bound therefore controls the full conjunction's synchronized product. -/
theorem cov_active_length {I : Instance k} {B : Reference k} {E : Ext I B}
    {c : Clause k} (X : Cov I B E c) (g : Nat) :
    (itemsAt I c X.D g).length <= activeBudget c := by
  rw [X.itemsAt_eq, List.length_map]
  unfold Cov.contribs
  rw [List.length_flatMap]
  refine Nat.le_trans (sum_map_le_sum_map (g := fun ai => 1 + (obsAt c ai).size) ?_) ?_
  . intro ai hai
    rw [List.length_map]
    exact Nat.le_trans (covered_count_le X ai (List.mem_range.mp hai) g)
      (X.freshCount_le (List.mem_range.mp hai))
  . have h := sum_map_affine 1 1 (fun ai => (obsAt c ai).size) (List.range c.atoms.length)
    exact Nat.le_of_eq (by simpa [activeBudget, RankQueryCoverage.sumSizes] using h)

theorem cov_compact {I : Instance k} {B : Reference k} {E : Ext I B}
    {c : Clause k} (X : Cov I B E c) : compact I c X.D = true :=
  (compact_iff I c X.D).mpr fun g _ => cov_active_length X g

/-- Coverage, not just soundness: every common-extension model supplies a
retained diagram. The extraction below is the existing coverage construction;
only cov_compact is new. -/
theorem coverage (I : Instance k) :
    forall B C, SafeReference I B -> FirstReturnExt I B C ->
      forall c, SatClause (prefixGraph I C) c ->
        exists D, Bounded c (RankQueryCoverage.budget c) D ∧
          compact I c D = true ∧ validDiagram I c D = true ∧
          SatClause (prefixGraph I B) (compileValid I c D) := by
  intro B C hB hC c hsat
  obtain ⟨E, hG⟩ := exists_ext I B C hB hC
  have hsat' : SatClause (prefixGraph I E.C) c := by
    show SatClause (prefixGraph I (extRef B ((E.a, E.p) :: E.rest))) c
    rw [← hG]
    exact hsat
  obtain ⟨tau, htests, hequal, hunequal, hatoms⟩ := hsat'
  have hentry : B.word.length + 1 < (prefixGraph I E.C).size :=
    Nat.succ_lt_succ E.m_lt_N
  have hch : forall ai, exists l : List NNode, forall h : ai < c.atoms.length,
      Consec (NStep (prefixGraph I E.C) (obsAt c ai)) l ∧
      (forall x ∈ l, NAllowed (prefixGraph I E.C) (obsAt c ai) x) ∧
      (exists q ∈ (obsAt c ai).initial, l.head? = some ((tau (c.atoms[ai]).source).val, q.val)) ∧
      (exists p ∈ (obsAt c ai).final, l.getLast? = some ((tau (c.atoms[ai]).target).val, p.val)) ∧
      visitsN (B.word.length + 1) l <= (obsAt c ai).size := by
    intro ai
    by_cases h : ai < c.atoms.length
    . have hacc := hatoms _ (List.getElem_mem h)
      obtain ⟨l, hl⟩ := chain_exists hacc ⟨B.word.length + 1, hentry⟩
      refine ⟨l, fun _ => ?_⟩
      rw [obsAt_eq h]
      exact hl
    . exact ⟨[], fun h' => absurd h' h⟩
  obtain ⟨chain, hspec⟩ := Classical.axiomOfChoice hch
  let X : Cov I B E c :=
    { τ := tau, tests := htests, equal := hequal, unequal := hunequal, chain := chain,
      chain_consec := fun ai h => (hspec ai h).1,
      chain_allowed := fun ai h => (hspec ai h).2.1,
      chain_head := fun ai h => (hspec ai h).2.2.1,
      chain_last := fun ai h => (hspec ai h).2.2.2.1,
      chain_visits := fun ai h => (hspec ai h).2.2.2.2 }
  exact ⟨X.D, X.bounded, cov_compact X, X.valid, X.sat⟩

end CoverageCount

/-! ## Reconstruction and the exact semantic equivalence -/

theorem reconstruction (I : Instance k) (phi : Query k) (B : Reference k)
    (hB : SafeReference I B) (h : Sat (prefixGraph I B) (preSmall I phi)) :
    exists C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) phi := by
  obtain ⟨out, hout, hsat⟩ := h
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hout
  obtain ⟨D, hb, _, hd⟩ := (mem_preClause I c out).mp hp
  apply RankQueryEnumeration.preimage_sound I RankQueryCoverage.budget phi B hB
  refine ⟨out, List.mem_flatMap.mpr ⟨c, hc, ?_⟩, hsat⟩
  exact (mem_preimageClause I c (RankQueryCoverage.budget c) out).mpr ⟨D, hb, hd⟩

theorem forward (I : Instance k) (phi : Query k) (B C : Reference k)
    (hB : SafeReference I B) (hC : FirstReturnExt I B C)
    (h : Sat (prefixGraph I C) phi) : Sat (prefixGraph I B) (preSmall I phi) := by
  obtain ⟨c, hc, hsat⟩ := h
  obtain ⟨D, hb, hcompact, hv, hs⟩ := coverage I B C hB hC c hsat
  refine ⟨compileValid I c D, List.mem_flatMap.mpr ⟨c, hc, ?_⟩, hs⟩
  apply (mem_preClause I c _).mpr
  exact ⟨D, hb, hcompact, by simp [compileDiagram, hv]⟩

theorem closure_iff (I : Instance k) (B : Reference k) (hB : SafeReference I B) (phi : Query k) :
    Sat (prefixGraph I B) (preSmall I phi) <->
      exists C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) phi := by
  constructor
  . exact reconstruction I phi B hB
  . rintro ⟨C, hC, hs⟩
    exact forward I phi B C hB hC hs

/-! ## Original numerical contract, for EVERY retained output clause -/

theorem compileValid_weight_le (I : Instance k) (c : Clause k) (D : Diagram k)
    (hb : Bounded c (RankQueryCoverage.budget c) D) (hcompact : compact I c D = true) :
    clauseWeight (compileValid I c D) <= closureBound k (clauseWeight c) := by
  let T := clauseWeight c
  let P := 2 * RankQueryCoverage.blockBound c
  let M := c.atoms.length * P
  have hT : 2 <= T := Nat.le_max_left _ _
  have hsum : 1 + c.vars + c.atoms.length + RankQuery.sumSizes c <= T := Nat.le_max_right _ _
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le I.initial.val) I.initial.isLt
  have hP : P <= 6 * T := by
    dsimp [P, RankQueryCoverage.blockBound]
    rw [coverage_sum_eq]
    omega
  have hM : M <= 6 * T ^ 2 := by
    calc
      M = c.atoms.length * P := rfl
      _ <= T * (6 * T) := Nat.mul_le_mul (by omega) hP
      _ = 6 * T ^ 2 := by simp [Nat.pow_succ, Nat.mul_left_comm]
  have hG : RankQueryCoverage.groupBound c <= 2 * T := by
    unfold RankQueryCoverage.groupBound
    rw [coverage_sum_eq]
    omega
  obtain ⟨_, hng, hnc, _, _, _, _, _, hpieces, _, _⟩ := hb
  have hn : D.groups <= 2 * T := Nat.le_trans hng hG
  have hcore : D.coreVars <= c.vars + M := by
    simpa [RankQueryCoverage.budget, RankQueryCoverage.coreBound, M, P,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnc
  have hp : forall ps ∈ D.pieces, ps.length <= P := fun ps hps => (hpieces ps hps).1
  have ho : forall a ∈ c.atoms, a.observer.size <= T := by
    intro a ha
    have hs : a.observer.size <= RankQuery.sumSizes c :=
      member_le_sum (List.mem_map.mpr ⟨a, ha, rfl⟩)
    omega
  have hem (g : Nat) : Estimate T g M (allEmitted I c D) :=
    allEmitted_estimate I c D P T hT ho hp g
  have hactive (g : Nat) (hg : g < D.groups - 1) : (itemsAt I c D g).length <= T := by
    have h := (compact_iff I c D).mp hcompact g hg
    unfold activeBudget at h
    rw [coverage_sum_eq] at h
    omega
  have hint (g : Nat) (hg : g < D.groups - 1) :
      (intervalAtom I c D g).observer.size <= 6 * k * T ^ T := by
    rw [interval_cardinality]
    apply Nat.mul_le_mul_left
    have hprod := prod_sizes_le (itemsAt I c D g) (hem g).activeSizes
    exact Nat.le_trans hprod (Nat.pow_le_pow_right (by omega) (hactive g hg))
  have hinterval : ((List.range (D.groups - 1)).map fun g => (intervalAtom I c D g).observer.size).sum <=
      12 * k * T ^ (T + 1) := by
    calc
      _ <= (List.range (D.groups - 1)).length * (6 * k * T ^ T) :=
        RankQueryCoverage.sum_map_le_const (fun g hg => hint g (List.mem_range.mp hg))
      _ <= (2 * T) * (6 * k * T ^ T) := Nat.mul_le_mul_right _ (by simp; omega)
      _ = 12 * k * T ^ (T + 1) := by
        change (2 * T) * (6 * k * T ^ T) = (2 * 6) * k * T ^ (T + 1)
        rw [Nat.pow_succ T T]
        ac_rfl
  have hMT : M * T <= 6 * T ^ 3 := by
    calc
      M * T <= (6 * T ^ 2) * T := Nat.mul_le_mul_right T hM
      _ = 6 * T ^ 3 := by simp [Nat.pow_succ, Nat.mul_assoc]
  have hvars : (compileValid I c D).vars <= 2 + 3 * T + M := by
    change 2 + D.groups + D.coreVars <= _
    omega
  have hatoms : (compileValid I c D).atoms.length <= 2 + M + 2 * T := by
    rw [compile_atoms_length]
    have := (hem 0).atoms
    omega
  have hsizes : RankQuery.sumSizes (compileValid I c D) <=
      4 + 6 * T ^ 3 + 12 * k * T ^ (T + 1) := by
    rw [compile_sum]
    have := (hem 0).sizes
    omega
  have hpoly : 9 + 5 * T + 12 * T ^ 2 + 6 * T ^ 3 <= 32 * T ^ 3 := by
    have h1 : 1 <= T ^ 3 := Nat.pow_pos (by omega)
    have ht : T <= T ^ 3 := by
      calc
        T = T ^ 1 := by simp
        _ <= T ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
    have ht2 : T ^ 2 <= T ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have hpow : T ^ 3 <= T ^ (2 * T + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hkp : T ^ (2 * T + 2) <= k * T ^ (2 * T + 2) := Nat.le_mul_of_pos_left _ hk
  have hmain : 32 * T ^ 3 <= 32 * k * T ^ (2 * T + 2) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 32 (Nat.le_trans hpow hkp)
  have hlast : 12 * k * T ^ (T + 1) <= 12 * k * T ^ (2 * T + 2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hraw : 1 + (compileValid I c D).vars + (compileValid I c D).atoms.length +
      RankQuery.sumSizes (compileValid I c D) <=
      32 * k * T ^ (2 * T + 2) + 12 * k * T ^ (2 * T + 2) := by
    omega
  have hpos : 0 < k * T ^ (2 * T + 2) := Nat.mul_pos hk (Nat.pow_pos (by omega))
  change max 2 (1 + (compileValid I c D).vars + (compileValid I c D).atoms.length +
    RankQuery.sumSizes (compileValid I c D)) <= 64 * k * T ^ (2 * T + 2)
  simp only [Nat.mul_assoc] at hraw ⊢
  omega

theorem preimage_clause_weight_le (I : Instance k) (phi : Query k) (out : Clause k)
    (hout : out ∈ preSmall I phi) : clauseWeight out <= closureBound k (weight phi) := by
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hout
  obtain ⟨D, hb, hcompact, hcompile⟩ := (mem_preClause I c out).mp hp
  unfold compileDiagram at hcompile
  split at hcompile
  . have he : out = compileValid I c D := (Option.some.inj hcompile).symm
    subst out
    apply Nat.le_trans (compileValid_weight_le I c D hb hcompact)
    apply RankQueryUnwind.closureBound_mono
    exact RankMilestones.le_maxNat (List.mem_map.mpr ⟨c, hc, rfl⟩)
  . contradiction

/-- Full original semantic-and-weight contract, with an effective compiler.
There is deliberately no shortest-witness theorem in this module. -/
theorem closureFor (I : Instance k) : ClosureFor I (preSmall I) :=
  ⟨fun phi B hB => closure_iff I B hB phi,
    fun phi out hout => preimage_clause_weight_le I phi out hout⟩

theorem closureStatement (I : Instance k) : ClosureStatement I := by
  intro _
  exact ⟨preSmall I, closureFor I⟩

theorem preSmall_nil (I : Instance k) : preSmall I [] = [] := rfl

/-- The preserved bad diagram is rejected without enumerating its enormous
observer state space or the enormous complete diagram union. -/
theorem old_counterexample_rejected :
    compact RankQueryWeightCounterexample.inst RankQueryWeightCounterexample.input
      RankQueryWeightCounterexample.diagram = false := by
  decide +kernel

end Subtail.SmallerCompilerAstra

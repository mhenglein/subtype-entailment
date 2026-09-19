import Subtail.RankQueryFinishTrace
import Subtail.RankQuerySemanticUnwind
import Subtail.RankWitnessReference

/-!
# Direct terminal decision by finite query promotion

A018/C080, issue #30. Original Witness semantics throughout. The finite
algorithm does not use a numerical witness bound or a query-weight premise.
-/
namespace Subtail.RankQueryDecision

open TerminalRank RankMilestones RankQuery RankQueryUnwind RankQueryEnumeration

variable {k : Nat}

/-- Executable safety test over exactly the positions of a finite reference. -/
def safeReferenceCheck (I : Instance k) (B : Reference k) : Bool :=
  decide (0 < B.word.length) && I.final.get (B.label 0) &&
  (List.finRange B.word.length).all (fun j =>
    decide (step I (B.label (j.val + 1)) B.word[j.val] = some (B.label j.val))) &&
  (List.range (B.word.length + 1)).all (fun j => !(I.bad.get (B.label j))) &&
  (List.range (B.word.length + 1)).all (fun j => !((mask I B j).get (B.label j)))

theorem safeReferenceCheck_correct (I : Instance k) (B : Reference k) :
    safeReferenceCheck I B = true ↔ SafeReference I B := by
  simp only [safeReferenceCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, true_implies, List.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨⟨⟨hn, hf⟩, hr⟩, hb⟩, hm⟩
    exact ⟨hn, hf, fun j hj => hr ⟨j, hj⟩, by simpa using hb, by simpa using hm⟩
  · intro h
    exact ⟨⟨⟨⟨h.nonempty, h.accepting⟩, fun j => h.run j.val j.isLt⟩, by simpa using h.safe⟩, by simpa using h.border⟩

/-- A total finite procedure. Correctness for witness existence requires
terminal final states; the definition itself accepts every finite instance. -/
def terminalWitnessCheck (I : Instance k) : Bool :=
  witnessCheck I [] ||
  let φ := promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2)
  [false, true].any fun a =>
    (List.finRange k).any fun f => (List.finRange k).any fun p =>
      safeReferenceCheck I (oneLetter a f p) &&
      satCheck (prefixGraph I (oneLetter a f p)) φ

theorem terminalWitnessCheck_spec (I : Instance k) :
    terminalWitnessCheck I = true ↔
      Witness I [] ∨ ∃ (a : Bool) (f p : Fin k),
        SafeReference I (oneLetter a f p) ∧
        Sat (prefixGraph I (oneLetter a f p))
          (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2)) := by
  simp [terminalWitnessCheck, Bool.or_eq_true, List.any_eq_true, List.mem_finRange,
    Bool.and_eq_true, witnessCheck_correct, safeReferenceCheck_correct,
    satCheck_correct]

/-- Every successful promoted finishing query reconstructs an original witness.
No rank bound or terminality is needed for this direction. -/
theorem promoted_finish_sound (I : Instance k) (B : Reference k)
    (hB : SafeReference I B) (h : Nat)
    (hs : Sat (prefixGraph I B)
      (promote (preimage I RankQueryCoverage.budget) (finishQuery I) h)) :
    ∃ w : Word, Witness I w := by
  obtain ⟨n, _, C, hc, hf⟩ :=
    (RankQuerySemanticUnwind.sat_promote_preimage_iff I (finishQuery I) h B hB).mp hs
  obtain ⟨ext, hw⟩ := RankQueryFinishTrace.finish_implies_witness I C
    (promotes_safe hB hc) hf
  exact ⟨_, hw⟩

theorem terminalWitnessCheck_sound (I : Instance k)
    (h : terminalWitnessCheck I = true) : ∃ w : Word, Witness I w := by
  rcases (terminalWitnessCheck_spec I).mp h with hw | ⟨a, f, p, hB, hs⟩
  · exact ⟨[], hw⟩
  · exact promoted_finish_sound I _ hB _ hs


/-- A nonempty word starts with a reference of literal rank one. -/
theorem rank_take_one (w : Word) (hw : 0 < w.length) :
    rank (w.take 1) = 1 := by
  cases w with
  | nil => simp at hw
  | cons a w =>
    simp [rank, positiveBorderCount, borderLengths, List.range_succ]

theorem first_milestone_positive {w : Word} {h m : Nat}
    (hh : 0 < h) (hm : FirstMilestone w h m) : 0 < m := by
  by_cases hz : m = 0
  · have hr := hm.2.1
    simp [hz] at hr
    omega
  · omega

theorem first_milestone_one {w : Word} {m : Nat}
    (hm : FirstMilestone w 1 m) : m = 1 := by
  have hp := first_milestone_positive (by omega : 0 < 1) hm
  have hr := rank_take_one w (by have := hm.1; omega)
  by_cases h : 1 < m
  · have := hm.2.2 1 h
    omega
  · omega

/-- The highest rank attained by a nonempty finite word has a first milestone. -/
theorem exists_maximal_milestone (w : Word) (hw : 0 < w.length) :
    ∃ H m, 0 < H ∧ FirstMilestone w H m ∧
      ∀ j, j ≤ w.length → rank (w.take j) ≤ H := by
  let ranks := (List.range (w.length + 1)).map (fun j => rank (w.take j))
  have hz : 0 ∈ ranks := by
    apply List.mem_map.mpr
    exact ⟨0, by simp, by simp⟩
  let H := maxNat ranks
  have hatt : H ∈ ranks := maxNat_mem hz
  obtain ⟨j, hj, hjr⟩ := List.mem_map.mp hatt
  have hjle : j ≤ w.length := by simpa [Nat.lt_succ_iff] using hj
  have hmax : ∀ i, i ≤ w.length → rank (w.take i) ≤ H := by
    intro i hi
    exact le_maxNat (List.mem_map.mpr ⟨i, by simp; omega, rfl⟩)
  have hpos : 0 < H := by
    have := hmax 1 (by omega)
    rw [rank_take_one w hw] at this
    omega
  obtain ⟨m, hm, _⟩ := exists_first_milestone hjle (by omega : H ≤ rank (w.take j))
  exact ⟨H, m, hpos, hm, hmax⟩

/-- Append one first-return promotion to a finite chain. -/
theorem promotes_snoc (I : Instance k) {n : Nat} {A B C : Reference k}
    (hc : Promotes I n A B) (hBC : FirstReturnExt I B C) :
    Promotes I (n + 1) A C := by
  induction hc with
  | refl B => exact Promotes.step hBC (Promotes.refl C)
  | step hAB hrest ih => exact Promotes.step hAB (ih hBC)


open RankWitnessReference

/-- Literal first returns between prefixes retain their safe state labels. -/
theorem prefix_firstReturnExt (I : Instance k) (C : Reference k)
    (hC : SafeReference I C) {m n : Nat} (hm : 0 < m)
    (hr : FirstReturn C.word m n) :
    FirstReturnExt I (prefixRef C m) (prefixRef C n) := by
  have hml : m ≤ C.word.length := by have := hr.1; have := hr.2.1; omega
  have hnl := hr.2.1
  have hmLen : (prefixRef C m).word.length = m := by
    simp [prefixRef, List.length_take_of_le hml]
  have hnLen : (prefixRef C n).word.length = n := by
    simp [prefixRef, List.length_take_of_le hnl]
  refine ⟨prefixRef_safe I hC (by have := hr.1; omega) hnl, ?_, ?_, ?_⟩
  · apply List.prefix_iff_eq_take.mpr
    simp [prefixRef, List.length_take_of_le hml, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hr.1)]
  · intro j _
    rfl
  · rw [hmLen, hnLen]
    refine ⟨hr.1, by rw [hnLen]; exact Nat.le_refl n, ?_, ?_⟩
    · simpa [prefixRef, List.take_take] using hr.2.2.1
    · intro j hmj hjn
      simpa [prefixRef, List.take_take, Nat.min_eq_left (Nat.le_of_lt hjn)]
        using hr.2.2.2 j hmj hjn

/-- The first rank-(h+1) milestone is reached in exactly h safe promotions. -/
theorem milestone_chain (I : Instance k) (C : Reference k)
    (hC : SafeReference I C) {h m : Nat}
    (hm : FirstMilestone C.word (h + 1) m) :
    Promotes I h (prefixRef C 1) (prefixRef C m) := by
  induction h generalizing m with
  | zero =>
    have he : m = 1 := first_milestone_one hm
    subst m
    exact Promotes.refl _
  | succ h ih =>
    obtain ⟨j, hj, _⟩ := exists_first_milestone hm.1
      (by have := hm.2.1; omega : h + 1 ≤ rank (C.word.take m))
    have hchain := ih hj
    have hreturn := milestones_are_first_returns (by omega : 0 < h + 1) hj hm
    exact promotes_snoc I hchain
      (prefix_firstReturnExt I C hC (first_milestone_positive (by omega) hj) hreturn)

/-- Every complete safe reference with bounded prefix rank satisfies the
promoted finishing query at its one-letter prefix. -/
theorem complete_reference_promotes_finish (I : Instance k) (C : Reference k)
    (hC : SafeReference I C)
    (hend : C.label C.word.length = I.initial)
    (hbound : ∀ j, j ≤ C.word.length → rank (C.word.take j) ≤ k - 1) :
    Sat (prefixGraph I (prefixRef C 1))
      (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2)) := by
  obtain ⟨H, m, hH, hm, hmax⟩ := exists_maximal_milestone C.word hC.nonempty
  have he := first_milestone_exact hH hm
  have hHbound : H ≤ k - 1 := by have := hbound m hm.1; omega
  have hmpos := first_milestone_positive hH hm
  have hB := prefixRef_safe I hC hmpos hm.1
  have hbase := prefixRef_safe I hC (by omega : 0 < 1) (by have := hC.nonempty; omega)
  have hfinish := RankQueryFinishTrace.maximal_rank_completion_finishes I
    (prefixRef C m) C hB hC
    ⟨List.take_prefix m C.word, fun _ _ => rfl⟩ hend
    (by intro j hj; change rank (C.word.take j) ≤ rank (C.word.take m); rw [he]; exact hmax j hj)
  have hmilestone : FirstMilestone C.word ((H - 1) + 1) m := by
    simpa [Nat.sub_add_cancel hH] using hm
  have hchain := milestone_chain I C hC hmilestone
  exact (RankQuerySemanticUnwind.sat_promote_preimage_iff I
    (finishQuery I) (k - 2) (prefixRef C 1) hbase).mpr
    ⟨H - 1, by omega, prefixRef C m, hchain, hfinish⟩

/-- A prefix reference and oneLetter may differ beyond their physical end;
only their word and endpoint-bounded labels are transported. -/
theorem prefix_oneLetter (I : Instance k) (C : Reference k)
    (hC : SafeReference I C) :
    ∃ (a : Bool) (f p : Fin k),
      SafeReference I (oneLetter a f p) ∧
      prefixGraph I (prefixRef C 1) = prefixGraph I (oneLetter a f p) := by
  cases hw : C.word with
  | nil => have := hC.nonempty; simp [hw] at this
  | cons a tail =>
    have hword : (prefixRef C 1).word = (oneLetter a (C.label 0) (C.label 1)).word := by
      simp [prefixRef, oneLetter, hw]
    have hl : ∀ j, j ≤ (prefixRef C 1).word.length →
        (prefixRef C 1).label j = (oneLetter a (C.label 0) (C.label 1)).label j := by
      intro j hj
      have hjle : j ≤ 1 := by simpa [prefixRef, hw] using hj
      have hz : j = 0 ∨ j = 1 := by omega
      rcases hz with rfl | rfl <;> simp [prefixRef, oneLetter]
    have hs := prefixRef_safe I hC (by omega : 0 < 1) (by simp [hw])
    exact ⟨a, C.label 0, C.label 1,
      RankQueryCoverage.safeReference_congr I hword hl hs,
      RankQueryCoverage.prefixGraph_congr I hword hl⟩

/-- Completeness uses terminal final states only for the prefix rank bound. -/
theorem terminalWitnessCheck_complete (I : Instance k) (ht : TerminalFinals I)
    {w : Word} (hw : Witness I w) : terminalWitnessCheck I = true := by
  apply (terminalWitnessCheck_spec I).mpr
  by_cases hne : w = []
  · exact Or.inl (hne ▸ hw)
  · right
    have hC := witnessRef_safe I hw hne
    have hf := hw.2.1
    simp only [stateAt, List.take_length] at hf
    cases hr : runFrom I I.initial w with
    | none => simp [hr, finalCheck] at hf
    | some f =>
      have hfinal : I.final.get f = true := by simpa [hr, finalCheck] using hf
      have hbound : ∀ j, j ≤ (witnessRef I w).word.length →
          rank ((witnessRef I w).word.take j) ≤ k - 1 := by
        intro j _
        exact reversed_prefix_rank_le I ht hr hfinal j
      have hs := complete_reference_promotes_finish I (witnessRef I w)
        hC (witnessRef_end I w) hbound
      obtain ⟨a, f', p, hB, he⟩ := prefix_oneLetter I (witnessRef I w) hC
      exact ⟨a, f', p, hB, he ▸ hs⟩

/-- The direct terminal rank-query decision statement, with no quantitative
closure or witness-bound hypothesis. -/
theorem rankDecisionStatement (I : Instance k) (ht : TerminalFinals I) :
    RankDecisionStatement I (preimage I RankQueryCoverage.budget) := by
  constructor
  · rintro ⟨w, hw⟩
    exact (terminalWitnessCheck_spec I).mp (terminalWitnessCheck_complete I ht hw)
  · intro h
    exact terminalWitnessCheck_sound I ((terminalWitnessCheck_spec I).mpr h)

/-- A total executable decision for existence of an original BorderAvoid
witness under terminal finals. This is not the arbitrary-tree subtype bridge. -/
theorem terminalWitnessCheck_correct (I : Instance k) (ht : TerminalFinals I) :
    terminalWitnessCheck I = true ↔ ∃ w : Word, Witness I w := by
  exact ⟨terminalWitnessCheck_sound I,
    fun ⟨_, hw⟩ => terminalWitnessCheck_complete I ht hw⟩

end Subtail.RankQueryDecision

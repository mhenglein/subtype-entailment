import Subtail.AbsorbingTerminal

/-!
# Bounded safe cycles for the absorbing continuation branch

This file proves the finite-cycle normalization used by C029.  It does not
bound the witness prefix and it does not claim that `InfWitness` is decidable.
-/

namespace Subtail
namespace InfiniteCycle

open AbsorbingTerminal

variable {k : Nat}

/- A safe prefix of an infinite-witness stem can be appended to its original
   witness while preserving the empty incoming column needed at the new
   endpoint.  If the appended stem is empty, the original nonempty cycle
   supplies that column instead. -/
theorem extend_witness_emptyIncoming (I : Instance k) (hA : Absorbing I)
    {u : Word} {q : Fin k} {v : Word} {r : Fin k} {c : Word} {d : Nat}
    {s : Fin k} (hu : Witness I u)
    (hq : stateAt I u u.length = some q)
    (hv : SafeRun I q v r) (hc : SafeRun I r c r) (hcne : c ≠ [])
    (hd : d ≤ c.length)
    (hpre : SafeRun I r (c.take d) s) :
    Witness I (u ++ (v ++ c.take d)) ∧
      stateAt I (u ++ (v ++ c.take d)) (u ++ (v ++ c.take d)).length = some s ∧
      (∀ p : Fin k, (I.flags.get p).get s = false) := by
  have hqfinal : I.final.get q = true := by
    simpa [finalCheck, hq] using hu.2.1
  have hstem : SafeRun I q (v ++ c.take d) s :=
    safeRun_append I hv hpre
  have hempty : ∀ p : Fin k, (I.flags.get p).get s = false := by
    by_cases hvne : v ≠ []
    · apply safeRun_emptyIncoming I hA hqfinal hstem
      intro hnil
      cases v with
      | nil => exact hvne rfl
      | cons a v => simp at hnil
    · have hvnil : v = [] := by simpa using hvne
      subst v
      by_cases hdpos : 0 < d
      · apply safeRun_emptyIncoming I hA hqfinal hstem
        apply List.ne_nil_of_length_pos
        simpa [List.length_take, Nat.min_eq_left hd] using hdpos
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hdpos
        subst d
        have hsr : s = r := by
          exact (Option.some.inj (by simpa [runFrom] using hpre.1)).symm
        have hrfinal : I.final.get r = true :=
          safeRun_final I hA hqfinal hv
        have hemptyR := safeRun_emptyIncoming I hA hrfinal hc hcne
        intro p
        simpa [hsr] using hemptyR p
  have hw : Witness I (u ++ (v ++ c.take d)) :=
    witness_append_safeRun I hA hu hq hstem
  have hrunU : runFrom I I.initial u = some q := by
    simpa [stateAt] using hq
  have hrunFull : runFrom I I.initial (u ++ (v ++ c.take d)) = some s := by
    rw [runFrom_append, hrunU]
    simpa using hstem.1
  have hstate :
      stateAt I (u ++ (v ++ c.take d)) (u ++ (v ++ c.take d)).length = some s := by
    simpa only [stateAt, List.take_length] using hrunFull
  exact ⟨hw, hstate, hempty⟩

/- The repeated-cut segment extracted from the first `k` letters is nonempty
   and has length at most `k`. -/
theorem safeRun_bounded_repeat_segment (I : Instance k)
    {q r : Fin k} {w : Word} (hw : SafeRun I q w r)
    (hwidth : w.length = k) :
    ∃ i j p, i < j ∧ j ≤ w.length ∧
      runFrom I q (w.take i) = some p ∧
      runFrom I q (w.take j) = some p ∧
      ((w.drop i).take (j - i)) ≠ [] ∧
      ((w.drop i).take (j - i)).length ≤ k := by
  have hbig : k ≤ w.length := by omega
  rcases safeRun_repeat_cut I hw hbig with ⟨i, j, p, hij, hj, hpi, hpj⟩
  have hne : ((w.drop i).take (j - i)) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega)]
    omega
  have hlen : ((w.drop i).take (j - i)).length ≤ k := by
    simp only [List.length_take, List.length_drop]
    exact Nat.le_trans (Nat.min_le_left _ _) (by omega)
  exact ⟨i, j, p, hij, hj, hpi, hpj, hne, hlen⟩

/- Main C029 normalization: under absorption, an infinitely continuable
   witness exists exactly when some original witness reaches a safe nonempty
   cycle of length at most the number of states, with an empty incoming flag
   column at the cycle base. -/
theorem infWitness_iff_bounded_cycle (I : Instance k) (hA : Absorbing I) :
    InfWitness I ↔
      ∃ w : Word, ∃ q : Fin k, ∃ c : Word,
        Witness I w ∧
        stateAt I w w.length = some q ∧
        (∀ p : Fin k, (I.flags.get p).get q = false) ∧
        SafeRun I q c q ∧
        c ≠ [] ∧
        c.length ≤ k := by
  constructor
  · rintro ⟨u, q, v, r, c, hu, hq, hv, hc, hcne⟩
    by_cases hshort : c.length ≤ k
    · have hpre : SafeRun I r (c.take 0) r := by
        apply safeRun_prefix I hc (by omega)
        simp [runFrom]
      rcases extend_witness_emptyIncoming I hA hu hq hv hc hcne
          (by omega) hpre with ⟨hw, hstate, hempty⟩
      refine ⟨u ++ (v ++ c.take 0), r, c, hw, hstate, hempty, hc, hcne, hshort⟩
    · have hbig : k < c.length := Nat.lt_of_not_ge hshort
      have hk : k ≤ c.length := Nat.le_of_lt hbig
      rcases hc.2 k hk with ⟨s, hsk, hsafe⟩
      have hprefix : SafeRun I r (c.take k) s :=
        safeRun_prefix I hc hk hsk
      have hprefix_len : (c.take k).length = k := by
        simp [List.length_take, Nat.min_eq_left hk]
      have hrep : k ≤ (c.take k).length := by omega
      rcases safeRun_bounded_repeat_segment I hprefix hprefix_len with
        ⟨i, j, p, hij, hj, hpi, hpj, hcycle_ne, hcycle_len⟩
      have hi : i ≤ k := by omega
      have hpi' : runFrom I r (c.take i) = some p := by
        have ht : (c.take k).take i = c.take i := by
          simp [List.take_take, Nat.min_eq_left hi]
        rw [← ht]
        exact hpi
      have hpre : SafeRun I r (c.take i) p :=
        safeRun_prefix I hc (by omega) hpi'
      have hcycle : SafeRun I p (((c.take k).drop i).take (j - i)) p :=
        safeRun_segment_of_equal_cut I hprefix (Nat.le_of_lt hij) hj hpi hpj
      rcases extend_witness_emptyIncoming I hA hu hq hv hc hcne
          (by omega) hpre with ⟨hw, hstate, hempty⟩
      refine ⟨u ++ (v ++ c.take i), p,
        (c.take k).drop i |>.take (j - i), hw, hstate, hempty, hcycle,
        hcycle_ne, hcycle_len⟩
  · rintro ⟨w, q, c, hw, hq, hflags, hc, hcne, hbound⟩
    have hsafe0 : safeCut I q c 0 := hc.2 0 (by omega)
    have hqSafe : safeState I q = true :=
      (safeCut_zero_iff I q c).mp hsafe0
    refine ⟨w, q, [], q, c, hw, hq, ?_, hc, hcne⟩
    refine ⟨by simp [runFrom], ?_⟩
    intro i hi
    have hi0 : i = 0 := by simp only [List.length_nil] at hi; omega
    subst i
    exact (safeCut_zero_iff I q []).2 hqSafe

end InfiniteCycle
end Subtail

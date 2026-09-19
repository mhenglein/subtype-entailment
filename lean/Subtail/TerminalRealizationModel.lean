import Subtail.TerminalRealization

/-!
Direct completeness for C030 by explicit arbitrary-tree languages.
Upper seeds use all prefix/run/suffix decompositions; the lower copy contains
forced nonfinal roots and transported ordered flag seeds. There is no call to
the forward subtype bridge or to a saturation algorithm.
-/
namespace Subtail
namespace TerminalRealization
open TreeSemantics

/-- The prefixes of suffixes at every occurrence of q on the supplied word. -/
def upperNodes (I : Instance k) (w : Word) (q : Fin k) (t : Word) : Prop :=
  ∃ x z, w = x ++ t ++ z ∧ runFrom I I.initial x = some q

theorem upper_closed (I : Instance k) (w : Word) (q : Fin k) :
    PrefixClosed (upperNodes I w q) := by
  intro u t
  rintro ⟨x, z, hw, hx⟩
  refine ⟨x, t ++ z, ?_, hx⟩
  simpa only [List.append_assoc] using hw

def upperTree (I : Instance k) (w : Word) (q : Fin k) : Tree :=
  ⟨upperNodes I w q, upper_closed I w q⟩

theorem witness_final_run (I : Instance k) {w : Word} (hw : Witness I w) :
    ∃ r, runFrom I I.initial w = some r ∧ I.final.get r = true := by
  have hh := hw.2.1
  simp only [stateAt, List.take_length] at hh
  cases hr : runFrom I I.initial w with
  | none => simp [finalCheck, hr] at hh
  | some r => exact ⟨r, hr, by simpa [finalCheck, hr] using hh⟩

theorem upper_next (I : Instance k) {w : Word} (hw : Witness I w)
    (q : Fin k) (c : Bool) (t : Word) (ht : upperNodes I w q (c :: t)) :
    ∃ r, step I q c = some r ∧ upperNodes I w r t := by
  rcases ht with ⟨x, z, he, hx⟩
  rcases witness_final_run I hw with ⟨f, hf, _⟩
  have hfull : runFrom I I.initial (x ++ (c :: (t ++ z))) = some f := by
    simpa only [he, List.append_assoc, List.cons_append] using hf
  have htail : runFrom I q (c :: (t ++ z)) = some f := by
    simpa [runFrom_append, hx] using hfull
  cases hs : step I q c with
  | none => simp [runFrom, hs] at htail
  | some r =>
    refine ⟨r, hs, x ++ [c], z, ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append, List.cons_append] using he
    · simp [runFrom_append, hx, runFrom, hs]

theorem upper_safe (I : Instance k) {w : Word} (hw : Witness I w)
    (q : Fin k) {t : Word} (ht : upperNodes I w q t) : I.bad.get q = false := by
  rcases ht with ⟨x, z, he, hx⟩
  have hi : x.length ≤ w.length := by simp [he, List.length_append]; omega
  have hq : stateAt I w x.length = some q := by
    simpa [stateAt, he, List.append_assoc] using hx
  have hh := hw.1 x.length hi
  cases hb : I.bad.get q <;> simp_all [safeCheck]

/-- Forced roots and all flag seeds propagated along defined transition paths. -/
def lowerNodes (I : Instance k) (w : Word) (q : Fin k) (t : Word) : Prop :=
  baseNodes I q t ∨ ∃ x y r p,
    t = x ++ y ∧ runFrom I q x = some r ∧
    (I.flags.get p).get r = true ∧ upperNodes I w p y

/-- A cut in x++y is strictly inside x, or leaves a prefix of y after x. -/
theorem cut_append (u t x y : Word) (h : u ++ t = x ++ y) :
    (∃ z, x = u ++ z ∧ z ≠ []) ∨ (∃ z, u = x ++ z ∧ y = z ++ t) := by
  induction u generalizing x with
  | nil =>
    cases x with
    | nil => exact Or.inr ⟨[], rfl, by simpa using h.symm⟩
    | cons c x => exact Or.inl ⟨c :: x, rfl, by simp⟩
  | cons c u ih =>
    cases x with
    | nil => exact Or.inr ⟨c :: u, rfl, by simpa using h.symm⟩
    | cons d x =>
      have hh : c = d ∧ u ++ t = x ++ y := by simpa using h
      rcases hh with ⟨rfl, hh⟩
      rcases ih x hh with ⟨z, hx, hz⟩ | ⟨z, hu, hy⟩
      · exact Or.inl ⟨z, by simp [hx], hz⟩
      · exact Or.inr ⟨z, by simp [hu], hy⟩

theorem lower_closed (I : Instance k) (ht : TerminalFinal I)
    (w : Word) (q : Fin k) : PrefixClosed (lowerNodes I w q) := by
  intro u t hu
  rcases hu with hb | ⟨x, y, r, p, he, hx, hg, hy⟩
  · exact Or.inl (base_closed I ht q u t hb)
  · rcases cut_append u t x y he with ⟨z, hz, hn⟩ | ⟨z, hu, hyz⟩
    · have hr : runFrom I q (u ++ z) = some r := by simpa only [hz] using hx
      rcases split_run I hr with ⟨q', hq', hr'⟩
      exact Or.inl ⟨q', hq', nonfinal_of_nonempty_run I ht hn hr'⟩
    · refine Or.inr ⟨x, z, r, p, hu, hx, hg, ?_⟩
      exact upper_closed I w p z t (by simpa only [hyz] using hy)

def lowerTree (I : Instance k) (ht : TerminalFinal I) (w : Word) (q : Fin k) : Tree :=
  ⟨lowerNodes I w q, lower_closed I ht w q⟩

theorem lower_root (I : Instance k) (w : Word) (q : Fin k)
    (hq : I.final.get q = false) : lowerNodes I w q [] :=
  Or.inl ⟨q, rfl, hq⟩

theorem lower_prepend (I : Instance k) (w : Word) (q r : Fin k)
    (c : Bool) (t : Word) (hs : step I q c = some r)
    (hm : lowerNodes I w r t) : lowerNodes I w q (c :: t) := by
  rcases hm with ⟨f, hf, hfin⟩ | ⟨x, y, f, p, he, hx, hg, hy⟩
  · exact Or.inl ⟨f, by simp [runFrom, hs, hf], hfin⟩
  · refine Or.inr ⟨c :: x, y, f, p, ?_, ?_, hg, hy⟩
    · simp [he]
    · simp [runFrom, hs, hx]

theorem flag_seed (I : Instance k) (w : Word) (p q : Fin k)
    (hg : (I.flags.get p).get q = true) (t : Word)
    (ht : upperNodes I w p t) : lowerNodes I w q t :=
  Or.inr ⟨[], t, q, p, rfl, rfl, hg, ht⟩

/-- A total tree valuation; it is a model when the supplied word is a witness. -/
def wordModel (I : Instance k) (ht : TerminalFinal I) (w : Word) :
    Valuation (2 * k + 1) := valuation (upperTree I w) (lowerTree I ht w)

theorem wordModel_models (I : Instance k) (ht : TerminalFinal I)
    (w : Word) (hw : Witness I w) : Models (constraints I) (wordModel I ht w) := by
  apply (models_iff_laws I _).mpr
  constructor
  · simp [wordModel, Holds, Below, bottom]
  · intro q
    refine ⟨?_, ?_, ?_, ?_⟩
    · change Below _ (product _ _)
      intro u hu
      have hau : upperNodes I w q u := by simpa [wordModel, upperTree] using hu
      cases u with
      | nil => exact product_root _ _
      | cons c u =>
        rcases upper_next I hw q c u hau with ⟨r, hs, hr⟩
        have hc : (wordModel I ht w (child a (step I q c))).nodes u := by
          simpa [wordModel, child, hs, upperTree] using hr
        cases c <;> exact hc
    · intro hq
      change Below (product _ _) _
      intro u hu
      change (valuation (upperTree I w) (lowerTree I ht w) (v q)).nodes u
      rw [valuation_v]
      change lowerNodes I w q u
      cases u with
      | nil => exact lower_root I w q hq
      | cons c u =>
        have hc : (wordModel I ht w (child v (step I q c))).nodes u := by
          cases c <;> exact hu
        cases hs : step I q c with
        | none =>
          have hf : False := by simpa [wordModel, child, hs, bottom] using hc
          exact False.elim hf
        | some r =>
          have hr : lowerNodes I w r u := by
            simpa [wordModel, child, hs, lowerTree] using hc
          exact lower_prepend I w q r c u hs hr
    · intro r hg u hu
      have hp : upperNodes I w q u := by simpa [wordModel, upperTree] using hu
      simpa [Holds, wordModel, lowerTree] using flag_seed I w q r hg u hp
    · intro hb u hu
      have hp : upperNodes I w q u := by simpa [wordModel, upperTree] using hu
      have hs := upper_safe I hw q hp
      simp_all

theorem wordModel_left (I : Instance k) (ht : TerminalFinal I) (w : Word) :
    (wordModel I ht w (a I.initial)).nodes w := by
  change (valuation (upperTree I w) (lowerTree I ht w) (a I.initial)).nodes w
  rw [valuation_a]
  exact ⟨[], [], by simp, rfl⟩

theorem wordModel_right (I : Instance k) (ht : TerminalFinal I)
    (w : Word) (hw : Witness I w) :
    ¬ (wordModel I ht w (v I.initial)).nodes w := by
  intro hmem
  have hlow : lowerNodes I w I.initial w := by
    simpa [wordModel, lowerTree] using hmem
  rcases hlow with ⟨r, hr, hf⟩ | ⟨x, y, r, p, he, hx, hg, hy⟩
  · have hh := hw.2.1
    simp [stateAt, finalCheck, hr, hf] at hh
  · rcases hy with ⟨u, z, hu, hup⟩
    have hlenx : w.length = x.length + y.length := by simp [he]
    have hlenu : w.length = u.length + y.length + z.length := by simp [hu]
    have hj : x.length ≤ w.length := by omega
    have hij : u.length ≤ x.length := by omega
    have hsi : stateAt I w u.length = some p := by
      simpa [stateAt, hu, List.append_assoc] using hup
    have hsj : stateAt I w x.length = some r := by simpa [stateAt, he] using hx
    have hag : Agrees w u.length x.length := by
      change (w.drop x.length).IsPrefix (w.drop u.length)
      have hi : w.drop u.length = y ++ z := by simp [hu, List.append_assoc]
      have hj' : w.drop x.length = y := by simp [he]
      rw [hi, hj']
      exact ⟨z, rfl⟩
    have hh := hw.2.2 x.length hj u.length hij hag
    simp [unflaggedCheck, hsi, hsj, hg] at hh

/-- Original Witness and model separation agree at each unchanged finite word. -/
theorem witness_iff_separating (I : Instance k) (ht : TerminalFinal I) (w : Word) :
    Witness I w ↔ ∃ rho, Models (constraints I) rho ∧
      (rho (a I.initial)).nodes w ∧ ¬ (rho (v I.initial)).nodes w := by
  constructor
  · intro hw
    exact ⟨wordModel I ht w, wordModel_models I ht w hw,
      wordModel_left I ht w, wordModel_right I ht w hw⟩
  · rintro ⟨rho, hm, ha, hv⟩
    exact separation_implies_witness I ht rho hm w ha hv

/-- The converse reduction preserves non-entailment over arbitrary trees. -/
theorem not_entails_iff_witness (I : Instance k) (ht : TerminalFinal I) :
    ¬ Entails (constraints I) (a I.initial) (v I.initial) ↔ ∃ w, Witness I w := by
  rw [not_entails_iff_separating]
  constructor
  · rintro ⟨rho, w, hm, ha, hv⟩
    exact ⟨w, (witness_iff_separating I ht w).mpr ⟨rho, hm, ha, hv⟩⟩
  · rintro ⟨w, hw⟩
    rcases (witness_iff_separating I ht w).mp hw with ⟨rho, hm, ha, hv⟩
    exact ⟨rho, w, hm, ha, hv⟩

end TerminalRealization
end Subtail

import Subtail.RankQuery

/-!
# Direct witnesses as safe reversed references
-/
namespace Subtail
namespace RankWitnessReference

open RankQuery
open TerminalRank
open RankMilestones

/-- The reversed word labelled by the original run's cut states. -/
def witnessRef (I : Instance k) (w : Word) : Reference k :=
  { word := w.reverse
    label := fun j => cutState I I.initial w (w.length - j) }

/-- A literal prefix of a labelled reference. -/
def prefixRef (B : Reference k) (n : Nat) : Reference k :=
  { word := B.word.take n
    label := B.label }

theorem witnessRef_end (I : Instance k) (w : Word) :
    (witnessRef I w).label (witnessRef I w).word.length = I.initial := by
  simp [witnessRef, cutState, runFrom]

theorem prefixRef_safe (I : Instance k) {B : Reference k}
    (hB : SafeReference I B) {n : Nat} (hn : 0 < n)
    (hle : n ≤ B.word.length) : SafeReference I (prefixRef B n) := by
  refine { nonempty := ?_, accepting := ?_, run := ?_, safe := ?_, border := ?_ }
  · simp [prefixRef, List.length_take, Nat.min_eq_left hle, hn]
  · simpa [prefixRef] using hB.accepting
  · intro j hj
    have hjn : j < n := by
      simpa [prefixRef, List.length_take, Nat.min_eq_left hle] using hj
    have hjB : j < B.word.length := Nat.lt_of_lt_of_le hjn hle
    simpa [prefixRef] using hB.run j hjB
  · intro j hj
    have hjn : j ≤ n := by
      simpa [prefixRef, List.length_take, Nat.min_eq_left hle] using hj
    have hjB : j ≤ B.word.length := Nat.le_trans hjn hle
    simpa [prefixRef] using hB.safe j hjB
  · intro j hj
    have hjn : j ≤ n := by
      simpa [prefixRef, List.length_take, Nat.min_eq_left hle] using hj
    have hjB : j ≤ B.word.length := Nat.le_trans hjn hle
    have hword : (B.word.take n).take j = B.word.take j := by
      rw [List.take_take, Nat.min_eq_left hjn]
    have hmask : mask I (prefixRef B n) j = mask I B j := by
      unfold mask prefixRef
      rw [hword]
    rw [hmask]
    exact hB.border j hjB

theorem reverse_border_agrees (w : Word) {j h : Nat} (hjl : j ≤ w.length)
    (hb : h ∈ borderLengths (w.reverse.take j)) :
    Agrees w (w.length - j) (w.length - h) := by
  have hseg : h ∈ borderLengths (w.drop (w.length - j)) := by
    have hr := border_reverse_of (w := w.reverse.take j) hb
    simpa [List.reverse_take, List.length_reverse, Nat.min_eq_left hjl] using hr
  obtain ⟨hbound, heq⟩ := mem_borderLengths.mp hseg
  have hle : h ≤ j := by
    simp only [List.length_drop] at hbound
    omega
  have hdrop_len : (w.drop (w.length - j)).length = j := by
    simp only [List.length_drop]
    omega
  have hright : (w.drop (w.length - j)).drop
      ((w.drop (w.length - j)).length - h) = w.drop (w.length - h) := by
    rw [hdrop_len, List.drop_drop]
    congr 1
    omega
  have hprefix : w.drop (w.length - h) =
      (w.drop (w.length - j)).take h := by
    calc
      w.drop (w.length - h) =
          (w.drop (w.length - j)).drop
            ((w.drop (w.length - j)).length - h) := hright.symm
      _ = (w.drop (w.length - j)).take h := heq.symm
  exact ⟨(w.drop (w.length - j)).drop h, by
    rw [hprefix]
    exact List.take_append_drop h (w.drop (w.length - j))⟩

theorem witnessRef_safe (I : Instance k) {w : Word} (hw : Witness I w)
    (hne : w ≠ []) : SafeReference I (witnessRef I w) := by
  have hlen : 0 < w.length := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons a t => simp
  have state_some : ∀ i, i ≤ w.length → ∃ q, stateAt I w i = some q := by
    intro i hi
    have hs := hw.1 i hi
    cases hq : stateAt I w i with
    | none => simp [safeCheck, hq] at hs
    | some q => exact ⟨q, rfl⟩
  have cut_eq {i : Nat} {q : Fin k} (hi : i ≤ w.length)
      (hs : stateAt I w i = some q) :
      cutState I I.initial w i = q := by
    have hs' : runFrom I I.initial (w.take i) = some q := by
      simpa [stateAt] using hs
    simp [cutState, hs']
  have step_at {i : Nat} (hi : i < w.length) {p q : Fin k}
      (hpi : stateAt I w i = some p)
      (hqi : stateAt I w (i + 1) = some q) :
      step I p (w[i]'hi) = some q := by
    have htake : w.take (i + 1) = w.take i ++ [w[i]'hi] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    have hs : stateAt I w (i + 1) =
        (stateAt I w i).bind (fun r => runFrom I r [w[i]'hi]) := by
      simp only [stateAt, htake, runFrom_append]
    rw [hpi] at hs
    rw [hqi] at hs
    simpa [runFrom] using hs.symm
  refine { nonempty := ?_, accepting := ?_, run := ?_, safe := ?_, border := ?_ }
  · simpa [witnessRef, List.length_reverse] using hlen
  · rcases state_some w.length (Nat.le_refl _) with ⟨q, hq⟩
    have hfinal : I.final.get q = true := by
      simpa [finalCheck, hq] using hw.2.1
    have hcut := cut_eq (Nat.le_refl _) hq
    simpa [witnessRef, hcut] using hfinal
  · intro j hj
    change j < w.reverse.length at hj
    have hjlen : j < w.reverse.length := hj
    have hjw : j < w.length := by
      simpa [List.length_reverse] using hjlen
    let i := w.length - 1 - j
    have hi : i < w.length := by
      dsimp [i]
      omega
    have hleft : w.length - (j + 1) = i := by
      dsimp [i]
      omega
    have hright : w.length - j = i + 1 := by
      dsimp [i]
      omega
    rcases state_some i (Nat.le_of_lt hi) with ⟨p, hp⟩
    rcases state_some (i + 1) (by omega) with ⟨q, hq⟩
    have hs := step_at hi hp hq
    have hcutp := cut_eq (Nat.le_of_lt hi) hp
    have hcutq := cut_eq (by omega : i + 1 ≤ w.length) hq
    have hletter : w.reverse[j] = w[i] := by
      rw [List.getElem_reverse hjlen]
    simpa [witnessRef, hleft, hright, hcutp, hcutq, hletter] using hs
  · intro j hj
    have hjw : j ≤ w.length := by
      simpa [witnessRef, List.length_reverse] using hj
    let i := w.length - j
    have hi : i ≤ w.length := by
      dsimp [i]
      omega
    rcases state_some i hi with ⟨q, hq⟩
    have hsafe := hw.1 i hi
    have hbad : I.bad.get q = false := by
      simpa [safeCheck, hq] using hsafe
    have hcut := cut_eq hi hq
    simpa [witnessRef, i, hcut] using hbad
  · intro j hj
    have hjw : j ≤ w.length := by
      simpa [witnessRef, List.length_reverse] using hj
    have hbad : ∀ h, h ∈ borderLengths (w.reverse.take j) →
        (I.flags.get (cutState I I.initial w (w.length - j))).get
          (cutState I I.initial w (w.length - h)) = false := by
      intro h hh
      have hag := reverse_border_agrees w hjw hh
      obtain ⟨hbound, _⟩ := mem_borderLengths.mp (show
        h ∈ borderLengths (w.reverse.take j) from hh)
      have hle : h ≤ j := by
        have hlen : (w.reverse.take j).length = j := by
          simp [List.length_reverse, Nat.min_eq_left hjw]
        omega
      have hi : w.length - j ≤ w.length := Nat.sub_le _ _
      have hq : w.length - h ≤ w.length := Nat.sub_le _ _
      rcases state_some (w.length - j) hi with ⟨p, hp⟩
      rcases state_some (w.length - h) hq with ⟨q, hq'⟩
      have hflag := hw.2.2 (w.length - h) hq (w.length - j)
        (by omega) hag
      have hflag' : unflaggedCheck I (some p) (some q) = true := by
        simpa [hp, hq'] using hflag
      have hfalse : (I.flags.get p).get q = false := by
        simpa [unflaggedCheck] using hflag'
      have hcutp := cut_eq hi hp
      have hcutq := cut_eq hq hq'
      simpa [hcutp, hcutq] using hfalse
    simp [mask, witnessRef, Vector.get, Vector.ofFn]
    intro h hh
    change (I.flags.get (cutState I I.initial w (w.length - j))).get
      (cutState I I.initial w (w.length - h)) = false
    exact hbad h hh

end RankWitnessReference
end Subtail

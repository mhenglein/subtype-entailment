import Subtail.PeriodicRun
/-! Finite and shifted periodic references for the C029 monitor. -/
namespace Subtail.PeriodicRotation
open PeriodicRun

theorem predecessor_succ_mod (d : Nat) (z : Fin d) :
    (((z.val + d - 1) % d) + 1) % d = z.val := by
  have hzlt := z.isLt
  have hd : 0 < d := by omega
  by_cases hz : z.val = 0
  · have hsub : d - 1 < d := by omega
    have heq : d - 1 + 1 = d := by omega
    simp [hz, Nat.mod_eq_of_lt hsub, heq]
  · have hpos : 0 < z.val := by omega
    have heq : z.val + d - 1 = (z.val - 1) + d := by omega
    have hsub : z.val - 1 < d := by omega
    have heq' : z.val - 1 + 1 = z.val := by omega
    simp [heq, Nat.mod_eq_of_lt hsub, heq', Nat.mod_eq_of_lt z.isLt]

theorem periodic_predecessor (c : Word) (z : Fin c.length) (t : Nat) :
    periodicStream c (((z.val + c.length - 1) % c.length) + (t+1)) =
      periodicStream c (z.val + t) := by
  have heq : (z.val + c.length - 1) % c.length + (t+1) =
      ((z.val + c.length - 1) % c.length + 1) + t := by omega
  unfold periodicStream
  rw [heq]
  have hm : ((((z.val + c.length - 1) % c.length) + 1) + t) % c.length =
      (z.val+t) % c.length := by
    calc
      _ = ((((z.val + c.length - 1) % c.length) + 1) % c.length + t % c.length) % c.length := Nat.add_mod _ _ _
      _ = (z.val + t % c.length) % c.length := by rw [predecessor_succ_mod]
      _ = (z.val + t) % c.length := by
        simpa only [Nat.mod_eq_of_lt z.isLt] using (Nat.add_mod z.val t c.length).symm
  rw [hm]

theorem periodic_rotation_iff (c : Word) (hc : c ≠ []) (x y : Nat) :
    (∀ t, t < c.length → periodicStream c (x+t) = periodicStream c (y+t)) ↔
      ∀ t, periodicStream c (x+t) = periodicStream c (y+t) := by
  constructor
  · intro h
    exact PeriodicTail.sameSuffix_of_eventually_periodic
      (d := c.length) (N := 0) (by cases c <;> simp_all)
      (fun t _ => periodicStream_periodic hc t) (by simpa using h)
  · exact fun h t _ => h t

/-- The cycle phase at the beginning of a word prepended to phase zero. -/
def alignedPhase (c : Word) (hc : 0 < c.length) : Word → Fin c.length
  | [] => ⟨0,hc⟩
  | _ :: w => ⟨((alignedPhase c hc w).val + c.length - 1) % c.length,
      Nat.mod_lt _ hc⟩

/-- The periodic reference aligned with the boundary after the finite word. -/
def reference (w c : Word) (hc : 0 < c.length) (t : Nat) : Bool :=
  periodicStream c ((alignedPhase c hc w).val + t)

theorem reference_cons_succ (w c : Word) (hc : 0 < c.length) (a : Bool) (t : Nat) :
    reference (a::w) c hc (t+1) = reference w c hc t := by
  exact periodic_predecessor c (alignedPhase c hc w) t

theorem prefixStream_cons_zero (w c : Word) (a : Bool) :
    prefixStream (a::w) c 0 = a := by
  simp [prefixStream]

theorem prefixStream_cons_succ (w c : Word) (a : Bool) (t : Nat) :
    prefixStream (a::w) c (t+1) = prefixStream w c t := by
  simp [prefixStream, Nat.add_lt_add_iff_right]

theorem reference_periodic (w c : Word) (hc : 0 < c.length) :
    PeriodicTail.Periodic (reference w c hc) c.length := by
  have hne : c ≠ [] := by intro h; simp [h] at hc
  intro t
  simpa [reference, Nat.add_assoc] using
    periodicStream_periodic hne ((alignedPhase c hc w).val+t)

theorem prefix_matches_reference (w c : Word) (hc : 0 < c.length) :
    PeriodicTail.MatchesFrom (prefixStream w c) (reference w c hc) w.length := by
  induction w with
  | nil => intro t ht; simp [prefixStream, reference, alignedPhase]
  | cons a w ih =>
    intro t ht
    have htpos : 0 < t := by simp only [List.length_cons] at ht; omega
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt htpos)
    rw [prefixStream_cons_succ, reference_cons_succ]
    exact ih n (by simp only [List.length_cons] at ht; omega)

theorem prefix_sameSuffix_iff (w c : Word) (hc : 0 < c.length)
    {i j : Nat} (hij : i < j) :
    PeriodicTail.SameSuffix (prefixStream w c) i j ↔
      PeriodicTail.MatchesFrom (prefixStream w c) (reference w c hc) i ∧
      PeriodicTail.SameSuffix (reference w c hc) i j :=
  PeriodicTail.eventually_sameSuffix_iff hc (reference_periodic w c hc)
    (prefix_matches_reference w c hc) hij

/-- The whole prefixed stream agrees with its aligned periodic reference. -/
def Matches (w c : Word) (hc : 0 < c.length) : Prop :=
  PeriodicTail.MatchesFrom (prefixStream w c) (reference w c hc) 0

theorem matches_nil (c : Word) (hc : 0 < c.length) : Matches [] c hc := by
  exact prefix_matches_reference [] c hc

theorem matches_cons_iff (w c : Word) (hc : 0 < c.length) (a : Bool) :
    Matches (a::w) c hc ↔ a = reference (a::w) c hc 0 ∧ Matches w c hc := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [prefixStream_cons_zero] using h 0 (by omega)
    · intro t ht
      simpa only [prefixStream_cons_succ, reference_cons_succ] using h (t+1) (by omega)
  · rintro ⟨ha, hw⟩ t ht
    cases t with
    | zero => simpa only [prefixStream_cons_zero] using ha
    | succ t =>
      simpa only [prefixStream_cons_succ, reference_cons_succ] using hw t (by omega)

theorem matches_of_sameSuffix (w c : Word) (hc : 0 < c.length) {j : Nat}
    (hj : 0 < j) (heq : PeriodicTail.SameSuffix (prefixStream w c) 0 j) :
    Matches w c hc := (prefix_sameSuffix_iff w c hc hj).mp heq |>.1

theorem sameSuffix_cons_succ_iff (w c : Word) (a : Bool) (i j : Nat) :
    PeriodicTail.SameSuffix (prefixStream (a::w) c) (i+1) (j+1) ↔
      PeriodicTail.SameSuffix (prefixStream w c) i j := by
  unfold PeriodicTail.SameSuffix
  have hshift (n t : Nat) : n+1+t = (n+t)+1 := by omega
  simp only [hshift, prefixStream_cons_succ]

end Subtail.PeriodicRotation

import Std

/-!
Exact finite graph reachability for C029. A round either reaches a fixed point
or grows the duplicate-free visited list. The complete state list supplies a
termination bound; this is not a cutoff on candidate prefix words.
The saturation argument is adapted from the existing RankQuery decision core.
-/
namespace Subtail.FiniteSearch

variable {α : Type} [DecidableEq α]

inductive Reach (succ : α → List α) (x : α) : α → Prop
  | refl : Reach succ x x
  | step {y z : α} : Reach succ x y → z ∈ succ y → Reach succ x z

def addNew (v : List α) : List α → List α
  | [] => v
  | y :: ys => addNew (if y ∈ v then v else y :: v) ys

def close (succ : α → List α) (v : List α) : List α :=
  addNew v (v.flatMap succ)

def iter (succ : α → List α) : Nat → List α → List α
  | 0, v => v
  | n + 1, v => iter succ n (close succ v)

def reachable (succ : α → List α) (all : List α) (x : α) : List α :=
  iter succ all.length [x]

variable (succ : α → List α)

theorem mem_addNew {v s : List α} {y : α} :
    y ∈ addNew v s ↔ y ∈ v ∨ y ∈ s := by
  induction s generalizing v with
  | nil => simp [addNew]
  | cons z zs ih =>
    simp only [addNew]
    rw [ih]
    by_cases hz : z ∈ v
    · simp only [hz, if_true, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hz)
        · exact Or.inr h
    · simp only [hz, if_false, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h

theorem nodup_addNew {v s : List α} (hv : v.Nodup) : (addNew v s).Nodup := by
  induction s generalizing v with
  | nil => simpa [addNew] using hv
  | cons z zs ih =>
    simp only [addNew]
    by_cases hz : z ∈ v
    · simpa only [hz, if_true] using ih hv
    · simp only [hz, if_false]
      exact ih (List.nodup_cons.mpr ⟨hz, hv⟩)

theorem length_addNew_le {v s : List α} : v.length ≤ (addNew v s).length := by
  induction s generalizing v with
  | nil => simp [addNew]
  | cons z zs ih =>
    simp only [addNew]
    by_cases hz : z ∈ v
    · simpa only [hz, if_true] using ih
    · simp only [hz, if_false]
      have h := ih (v := z :: v)
      simp only [List.length_cons] at h
      omega

/-- If a saturation round adds nothing, every offered node was already present. -/
theorem addNew_eq_subset {v s : List α} (h : addNew v s = v) :
    ∀ y ∈ s, y ∈ v := by
  induction s generalizing v with
  | nil => simp
  | cons z zs ih =>
    intro y hy
    simp only [addNew] at h
    by_cases hz : z ∈ v
    · simp only [hz, if_true] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hz
      · exact ih h y hy
    · exfalso
      simp only [hz, if_false] at h
      have hl := congrArg List.length h
      have hle := length_addNew_le (v := z :: v) (s := zs)
      simp only [List.length_cons] at hle hl
      omega

theorem addNew_ne_lt {v s : List α} (h : addNew v s ≠ v) :
    v.length < (addNew v s).length := by
  induction s generalizing v with
  | nil => exact absurd rfl h
  | cons z zs ih =>
    simp only [addNew] at h ⊢
    by_cases hz : z ∈ v
    · simp only [hz, if_true] at h ⊢
      exact ih h
    · simp only [hz, if_false] at h ⊢
      have hle := length_addNew_le (v := z :: v) (s := zs)
      simp only [List.length_cons] at hle
      omega

/-- Every node of a saturation is a genuine run from the seed. -/
theorem run_of_mem_iter {x : α} :
    ∀ (n : Nat) (v : List α), (∀ z ∈ v, Reach succ x z) →
      ∀ y ∈ iter succ n v, Reach succ x y := by
  intro n
  induction n with
  | zero => intro v hv y hy; exact hv y hy
  | succ n ih =>
    intro v hv y hy
    apply ih (close succ v) _ y hy
    intro z hz
    rcases (mem_addNew).mp hz with hz | hz
    · exact hv z hz
    · obtain ⟨w, hw, hzw⟩ := List.mem_flatMap.mp hz
      exact Reach.step (hv w hw) hzw

theorem subset_close {v : List α} : ∀ y ∈ v, y ∈ close succ v := by
  intro y hy
  exact (mem_addNew).mpr (Or.inl hy)

theorem subset_iter {v : List α} : ∀ n, ∀ y ∈ v, y ∈ iter succ n v := by
  intro n
  induction n generalizing v with
  | zero => intro y hy; exact hy
  | succ n ih => intro y hy; exact ih y (subset_close succ y hy)

theorem nodup_iter {v : List α} (hv : v.Nodup) : ∀ n, (iter succ n v).Nodup := by
  intro n
  induction n generalizing v with
  | zero => exact hv
  | succ n ih => exact ih (nodup_addNew hv)

/-- Closed under successors: the invariant that makes saturation complete. -/
def IsClosed (v : List α) : Prop := ∀ z ∈ v, ∀ y, y ∈ succ z → y ∈ v

theorem isClosed_of_fixed {v : List α} (h : close succ v = v) : IsClosed succ v := by
  intro z hz y hs
  apply addNew_eq_subset h
  exact List.mem_flatMap.mpr ⟨z, hz, hs⟩

theorem iter_of_fixed {v : List α} (h : close succ v = v) : ∀ n, iter succ n v = v := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, h, ih]

/-- Either saturation has already closed, or it has grown by one node per round. -/
theorem closed_or_grow {v : List α} :
    ∀ n, IsClosed succ (iter succ n v) ∨ v.length + n ≤ (iter succ n v).length := by
  intro n
  induction n generalizing v with
  | zero => exact Or.inr (by simp [iter])
  | succ n ih =>
    by_cases hf : close succ v = v
    · left
      rw [iter, hf, iter_of_fixed succ hf]
      exact isClosed_of_fixed succ hf
    · rcases ih (v := close succ v) with hc | hl
      · exact Or.inl hc
      · right
        have hlt := addNew_ne_lt hf
        simp only [iter]
        change v.length + (n + 1) ≤ (iter succ n (close succ v)).length
        change v.length < (close succ v).length at hlt
        omega

theorem isClosed_reachable (all : List α) (hAll : ∀ a, a ∈ all) (x : α) : IsClosed succ (reachable succ all x) := by
  rcases closed_or_grow succ (v := [x]) all.length with hc | hl
  · exact hc
  · exfalso
    have hn := nodup_iter succ (v := [x]) (by simp) all.length
    have hle := hn.length_le_of_subset (l₂ := all) (fun y _ => hAll y)
    simp only [List.length_singleton] at hl
    omega

omit [DecidableEq α] in
theorem mem_of_run_closed {S : List α} (hS : IsClosed succ S) {x y : α}
    (hx : x ∈ S) (hr : Reach succ x y) : y ∈ S := by
  induction hr with
  | refl => exact hx
  | step _ hs ih => exact hS _ ih _ hs

theorem mem_reachable_iff (all : List α) (hAll : ∀ a, a ∈ all) {x y : α} :
    y ∈ reachable succ all x ↔ Reach succ x y := by
  constructor
  · intro hy
    refine run_of_mem_iter succ _ [x] ?_ y hy
    intro z hz
    simp only [List.mem_singleton] at hz
    subst hz
    exact Reach.refl
  · intro hr
    exact mem_of_run_closed succ (isClosed_reachable succ all hAll x)
      (subset_iter succ _ x (by simp)) hr


/-- Stop once a round changes nothing; the supplied fuel still ensures totality. -/
def saturate : Nat → List α → List α
  | 0, v => v
  | n + 1, v =>
    let next := close succ v
    if next = v then v else saturate n next

theorem saturate_eq_iter (n : Nat) (v : List α) :
    saturate succ n v = iter succ n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [saturate]
    split
    · next h => rw [iter, h, iter_of_fixed succ h]
    · exact ih _

def reachesAny (all : List α) (x : α) (accept : α → Bool) : Bool :=
  (saturate succ all.length [x]).any accept

theorem reachesAny_correct (all : List α) (hAll : ∀ a, a ∈ all)
    (x : α) (accept : α → Bool) :
    reachesAny succ all x accept = true ↔
      ∃ y, Reach succ x y ∧ accept y = true := by
  simp only [reachesAny, saturate_eq_iter, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, ha⟩
    exact ⟨y, (mem_reachable_iff succ all hAll).mp hy, ha⟩
  · rintro ⟨y, hy, ha⟩
    exact ⟨y, (mem_reachable_iff succ all hAll).mpr hy, ha⟩

/-- A cardinal bound can be computed without materializing all states. Its
completeness proof still refers to the explicit finite enumeration. -/
def reachesAnyWithFuel (fuel : Nat) (x : α) (accept : α → Bool) : Bool :=
  (saturate succ fuel [x]).any accept

theorem reachesAnyWithFuel_correct (all : List α) (hAll : ∀ a, a ∈ all)
    (fuel : Nat) (hFuel : all.length ≤ fuel) (x : α) (accept : α → Bool) :
    reachesAnyWithFuel succ fuel x accept = true ↔
      ∃ y, Reach succ x y ∧ accept y = true := by
  have hc : IsClosed succ (iter succ fuel [x]) := by
    rcases closed_or_grow succ (v := [x]) fuel with hc | hg
    · exact hc
    · have hn := nodup_iter succ (v := [x]) (by simp) fuel
      have hle := hn.length_le_of_subset (l₂ := all) (fun y _ => hAll y)
      simp only [List.length_singleton] at hg
      omega
  simp only [reachesAnyWithFuel, saturate_eq_iter, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, ha⟩
    refine ⟨y, ?_, ha⟩
    apply run_of_mem_iter succ fuel [x] _ y hy
    intro z hz
    have hz' : z = x := List.mem_singleton.mp hz
    subst z
    exact Reach.refl
  · rintro ⟨y, hy, ha⟩
    refine ⟨y, mem_of_run_closed succ hc ?_ hy, ha⟩
    exact subset_iter succ fuel x (by simp)

end Subtail.FiniteSearch

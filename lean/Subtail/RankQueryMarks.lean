import Subtail.RankQueryFirstReturn

/-!
# Global physical marks for stage-4b completeness

Support for A018/C080 issue #28.  This module deliberately works with PHYSICAL
graph positions (natural-number vertex indices), not KMP cursor values.  It
collects query-variable positions, the two root/end anchors, and both endpoints
of every already-extracted maximal fresh-forward interval into one global
deduplicated list ordered by physical position.

The extraction of maximal intervals from product-simple atom chains is a
separate next lemma.  No diagram enumerator or Closure Lemma is assumed here.
-/
namespace Subtail
namespace RankQueryMarks

open RankQuery RankQueryFirstReturn

/-- One maximal physical-forward fresh interval, represented by its physical
start and end vertex positions. -/
abbrev Segment := Nat × Nat

/-- Both physical endpoints of every segment. -/
def segmentEnds (xs : List Segment) : List Nat :=
  xs.flatMap fun x => [x.1, x.2]

/-- Endpoints contributed by all observer atoms. -/
def allSegmentEnds (families : List (List Segment)) : List Nat :=
  families.flatMap segmentEnds

/-- Raw global marks before deduplication. -/
def rawMarks (vars : List Nat) (root endpoint : Nat)
    (families : List (List Segment)) : List Nat :=
  vars ++ [root, endpoint] ++ allSegmentEnds families

/-- Canonical global physical marks: scan physical vertices in increasing order
and retain exactly those occurring in the raw mark multiset.  Equal cursor
values play no role in this definition. -/
def physicalMarks (N : Nat) (raw : List Nat) : List Nat :=
  (List.range N).filter fun j => decide (j ∈ raw)

theorem segmentEnds_length (xs : List Segment) :
    (segmentEnds xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [segmentEnds]
  | cons x xs ih =>
    simp [segmentEnds, ih]
    omega

theorem allSegmentEnds_length (families : List (List Segment)) :
    (allSegmentEnds families).length =
      2 * (families.map List.length).sum := by
  induction families with
  | nil => simp [allSegmentEnds]
  | cons xs rest ih =>
    simp [allSegmentEnds, segmentEnds_length, ih]
    omega

theorem rawMarks_length (vars : List Nat) (root endpoint : Nat)
    (families : List (List Segment)) :
    (rawMarks vars root endpoint families).length =
      vars.length + 2 + 2 * (families.map List.length).sum := by
  simp [rawMarks, allSegmentEnds_length]
  omega

/-- Pointwise interval-count bounds paired with observer sizes. -/
inductive FamiliesBound : List Nat → List (List Segment) → Prop
  | nil : FamiliesBound [] []
  | cons {s : Nat} {sizes : List Nat} {xs : List Segment}
      {families : List (List Segment)} :
      xs.length ≤ s + 1 → FamiliesBound sizes families →
      FamiliesBound (s :: sizes) (xs :: families)

theorem FamiliesBound.length_eq {sizes : List Nat}
    {families : List (List Segment)} (h : FamiliesBound sizes families) :
    sizes.length = families.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem FamiliesBound.sum_lengths_le {sizes : List Nat}
    {families : List (List Segment)} (h : FamiliesBound sizes families) :
    (families.map List.length).sum ≤
      (sizes.map fun s => s + 1).sum := by
  induction h with
  | nil => simp
  | @cons s sizes xs families hx _ ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The raw global mark multiset obeys the candidate's
`v + 2 + 2 * sum_i (s_i+1)` bound. -/
theorem rawMarks_length_le (vars : List Nat) (root endpoint : Nat)
    {sizes : List Nat} {families : List (List Segment)}
    (h : FamiliesBound sizes families) :
    (rawMarks vars root endpoint families).length ≤
      vars.length + 2 + 2 * (sizes.map fun s => s + 1).sum := by
  rw [rawMarks_length]
  have hs := h.sum_lengths_le
  omega

theorem physicalMarks_nodup (N : Nat) (raw : List Nat) :
    (physicalMarks N raw).Nodup := by
  exact List.Pairwise.filter _ List.nodup_range

theorem mem_physicalMarks {N x : Nat} {raw : List Nat} :
    x ∈ physicalMarks N raw ↔ x < N ∧ x ∈ raw := by
  simp [physicalMarks, List.mem_filter, List.mem_range]

/-- Every in-range raw physical position is retained globally. -/
theorem mem_physicalMarks_of_mem {N x : Nat} {raw : List Nat}
    (hN : x < N) (hx : x ∈ raw) : x ∈ physicalMarks N raw :=
  mem_physicalMarks.mpr ⟨hN, hx⟩

/-- Deduplicating/ordering by physical position never increases the mark count. -/
theorem physicalMarks_length_le_raw (N : Nat) (raw : List Nat) :
    (physicalMarks N raw).length ≤ raw.length := by
  have hnd := physicalMarks_nodup N raw
  exact hnd.length_le_of_subset (fun x hx => (mem_physicalMarks.mp hx).2)

/-- Final global physical-mark bound.  This statement is independent of cursor
aliasing because its entire domain is the concrete vertex position. -/
theorem physicalMarks_length_le (N : Nat) (vars : List Nat)
    (root endpoint : Nat) {sizes : List Nat}
    {families : List (List Segment)} (h : FamiliesBound sizes families) :
    (physicalMarks N (rawMarks vars root endpoint families)).length ≤
      vars.length + 2 + 2 * (sizes.map fun s => s + 1).sum := by
  exact Nat.le_trans (physicalMarks_length_le_raw N _)
    (rawMarks_length_le vars root endpoint h)

/-- Query-variable positions are retained whenever they are genuine graph
vertices. -/
theorem variable_mem_global {N : Nat} {vars : List Nat}
    {root endpoint : Nat} {families : List (List Segment)}
    {x : Nat} (hx : x ∈ vars) (hN : x < N) :
    x ∈ physicalMarks N (rawMarks vars root endpoint families) := by
  apply mem_physicalMarks_of_mem hN
  simp [rawMarks, hx]

/-- Both distinguished anchors are retained when in range. -/
theorem anchors_mem_global {N : Nat} {vars : List Nat}
    {root endpoint : Nat} {families : List (List Segment)}
    (hr : root < N) (he : endpoint < N) :
    root ∈ physicalMarks N (rawMarks vars root endpoint families) ∧
    endpoint ∈ physicalMarks N (rawMarks vars root endpoint families) := by
  constructor
  · apply mem_physicalMarks_of_mem hr
    simp [rawMarks]
  · apply mem_physicalMarks_of_mem he
    simp [rawMarks]

end RankQueryMarks
end Subtail

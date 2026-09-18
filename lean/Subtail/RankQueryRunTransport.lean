import Subtail.RankQuerySound

/-!
# Generic run transport helpers for rank-query reconstruction

Support for A018 stage 4c (issue #29).  This module is deliberately disjoint
from the active compiler proof.  It proves graph-independent path lemmas needed
to reassemble one original observer run from compiled pieces.

No statement of the Closure Lemma is assumed here.
-/
namespace Subtail
namespace RankQueryRunTransport

open RankQuery RankQueryCompiler

variable {k : Nat}

/-- Runs concatenate when the endpoint/control seam is literally the same node. -/
theorem run_trans {G : Graph k} {O : Observer k} {x y z : Node G O}
    (hxy : Run G O x y) (hyz : Run G O y z) : Run G O x z := by
  induction hyz with
  | refl _ => exact hxy
  | step _ hs ih => exact Run.step ih hs

/-- A finite simulation between observer products.  It maps both graph vertices
and observer controls, preserving allowed nodes and individual directed steps. -/
structure Simulation (G H : Graph k) (O P : Observer k) where
  vertex : Fin G.size → Fin H.size
  control : Fin O.size → Fin P.size
  allowed : ∀ x : Node G O, Allowed G O x →
    Allowed H P (vertex x.1, control x.2)
  step : ∀ x y : Node G O, Step G O x y →
    Step H P (vertex x.1, control x.2) (vertex y.1, control y.2)

/-- A simulation transports an entire run, not merely one edge. -/
theorem Simulation.run {G H : Graph k} {O P : Observer k}
    (S : Simulation G H O P) {x y : Node G O} (h : Run G O x y) :
    Run H P (S.vertex x.1, S.control x.2) (S.vertex y.1, S.control y.2) := by
  induction h with
  | refl hx => exact Run.refl (S.allowed _ hx)
  | step _ hs ih => exact Run.step ih (S.step _ _ hs)

/-- If initial/final controls are also preserved, accepted directed paths
transport through the simulation. -/
theorem Simulation.accepts {G H : Graph k} {O P : Observer k}
    (S : Simulation G H O P)
    (hinit : ∀ q ∈ O.initial, S.control q ∈ P.initial)
    (hfinal : ∀ q ∈ O.final, S.control q ∈ P.final)
    {u v : Fin G.size} (h : Accepts G O u v) :
    Accepts H P (S.vertex u) (S.vertex v) := by
  obtain ⟨q, hq, p, hp, hr⟩ := h
  exact ⟨S.control q, hinit q hq, S.control p, hfinal p hp, S.run hr⟩

/-- Slicing changes only the initial/final lists, never Allowed. -/
theorem allowed_slice_iff (G : Graph k) (o : Observer k) (lc rc : Fin o.size)
    (x : Node G o) :
    Allowed G (sliceObs o lc rc) x ↔ Allowed G o x := by
  rfl

/-- Slicing changes only the initial/final lists, never Step. -/
theorem step_slice_iff (G : Graph k) (o : Observer k) (lc rc : Fin o.size)
    (x y : Node G o) :
    Step G (sliceObs o lc rc) x y ↔ Step G o x y := by
  rfl

/-- Slicing an observer changes only its permitted initial/final controls.
The run relation itself is unchanged. -/
def sliceToBase (G : Graph k) (o : Observer k) (lc rc : Fin o.size) :
    Simulation G G (sliceObs o lc rc) o where
  vertex := id
  control := id
  allowed := by
    intro x hx
    exact (allowed_slice_iff G o lc rc x).mp hx
  step := by
    intro x y hxy
    exact (step_slice_iff G o lc rc x y).mp hxy

/-- Conversely, the base observer run relation is unchanged by slicing. -/
def baseToSlice (G : Graph k) (o : Observer k) (lc rc : Fin o.size) :
    Simulation G G o (sliceObs o lc rc) where
  vertex := id
  control := id
  allowed := by
    intro x hx
    exact (allowed_slice_iff G o lc rc x).mpr hx
  step := by
    intro x y hxy
    exact (step_slice_iff G o lc rc x y).mpr hxy

/-- Acceptance of a slice is exactly one base-observer run between the selected
seam controls.  This is the form used when concatenating diagram pieces. -/
theorem accepts_slice_iff (G : Graph k) (o : Observer k)
    (lc rc : Fin o.size) (u v : Fin G.size) :
    Accepts G (sliceObs o lc rc) u v ↔ Run G o (u, lc) (v, rc) := by
  constructor
  · rintro ⟨q, hq, p, hp, hr⟩
    simp only [sliceObs, List.mem_singleton] at hq hp
    subst q
    subst p
    exact (sliceToBase G o lc rc).run hr
  · intro hr
    refine ⟨lc, ?_, rc, ?_, ?_⟩
    · change lc ∈ [lc]
      exact List.mem_singleton.mpr rfl
    · change rc ∈ [rc]
      exact List.mem_singleton.mpr rfl
    · exact (baseToSlice G o lc rc).run hr

/-- Three already-transported pieces with exact seam nodes reassemble into one
run.  Kept explicit because this is the shape repeatedly used by portal diagrams. -/
theorem run_trans3 {G : Graph k} {O : Observer k} {a b c d : Node G O}
    (hab : Run G O a b) (hbc : Run G O b c) (hcd : Run G O c d) :
    Run G O a d :=
  run_trans (run_trans hab hbc) hcd

end RankQueryRunTransport
end Subtail

import Subtail.RankQueryReconstruction

namespace Subtail
namespace RankQueryReconstruction
open RankQuery

/-! ## Finite families of observations, without a hidden-state quantifier swap -/

def mapNode (G : Graph k) {m n : Nat} (f : Fin m -> Fin n)
    (x : Fin G.size × Fin m) : Fin G.size × Fin n := (x.1,f x.2)

def mapTrace (G : Graph k) {m n : Nat} (f : Fin m -> Fin n)
    (ts : List (Label × (Fin G.size × Fin m))) : List (Label × (Fin G.size × Fin n)) :=
  ts.map fun t => (t.1,mapNode G f t.2)

theorem mapTrace_id (G : Graph k) (A : Observer k) (ts : List (Label × Node G A)) :
    mapTrace G (fun q => q) ts = ts := by
  simp [mapTrace,mapNode]

theorem mapTrace_comp (G : Graph k) {a m n : Nat}
    (f : Fin m -> Fin a) (g : Fin n -> Fin m)
    (ts : List (Label × (Fin G.size × Fin n))) :
    mapTrace G f (mapTrace G g ts) = mapTrace G (fun q => f (g q)) ts := by
  simp [mapTrace,mapNode,List.map_map]

def pullObservation {A M : Observer k} (f : Fin M.size -> Fin A.size)
    (V : Observation A) : Observation M where
  observer := V.observer
  colour := fun q c => V.colour (f q) c
  labels := fun q c l d p => V.labels (f q) c l d (f p)

/-- Sound projection does not identify distinct hidden generator paths. -/
theorem observes_pull_sound {G : Graph k} {A M : Observer k}
    (f : Fin M.size -> Fin A.size) (V : Observation A) {x y q p ts}
    (h : Observes G M (pullObservation f V) x q ts y p) :
    Observes G A V (mapNode G f x) q (mapTrace G f ts) (mapNode G f y) p := by
  induction h with
  | nil hx => exact .nil hx
  | cons hx hs ht ih => exact .cons hx hs ih

/-- Reverse lifting requires the ACTUAL generator trace. Merely knowing the
projected endpoints are equal would be unsound for an empty trace. -/
theorem observes_pull_complete {G : Graph k} {A M : Observer k}
    (f : Fin M.size -> Fin A.size) (V : Observation A) {x y ts}
    (h : TraceRun G M x ts y) :
    ∀ q p, Observes G A V (mapNode G f x) q (mapTrace G f ts) (mapNode G f y) p ->
      Observes G M (pullObservation f V) x q ts y p := by
  induction h with
  | nil hx =>
    intro q p hv
    cases hv with
    | nil hq => exact .nil hq
  | cons hx hs ht ih =>
    intro q p hv
    cases hv with
    | cons hq hm ht' => exact .cons hq hm (ih _ _ ht')

/-- All internal generator coordinates are retained while observers are added. -/
structure Bundle (A : Observer k) where
  machine : Observer k
  projection : Fin machine.size -> Fin A.size

def emptyBundle (A : Observer k) : Bundle A := ⟨A,fun q => q⟩

def extendBundle {A : Observer k} (M : Bundle A) (V : Observation A) : Bundle A where
  machine := synchronize M.machine (pullObservation M.projection V)
  projection := fun i => M.projection (pairAt M.machine (pullObservation M.projection V) i).1

/-- A finite list is compiled recursively; all returned observers are finite data. -/
def bundle (A : Observer k) : List (Observation A) -> Bundle A
  | [] => emptyBundle A
  | V::Vs => extendBundle (bundle A Vs) V

def ObservationAccepts (G : Graph k) (A : Observer k) (V : Observation A)
    (x : Node G A) (ts : List (Label × Node G A)) (y : Node G A) : Prop :=
  ∃ q ∈ V.observer.initial, ∃ p ∈ V.observer.final, Observes G A V x q ts y p

/-- The generator's complete projected trace is fixed, not just its word. -/
def Realizes (G : Graph k) (A : Observer k) (M : Bundle A)
    (x : Node G A) (ts : List (Label × Node G A)) (y : Node G A) : Prop :=
  ∃ i ∈ M.machine.initial, ∃ j ∈ M.machine.final, ∃ us,
    M.projection i = x.2 ∧ M.projection j = y.2 ∧
    mapTrace G M.projection us = ts ∧
    TraceRun G M.machine (x.1,i) us (y.1,j)

/-- Adding an observer intersects requirements on ONE trace, not independent paths. -/
theorem realizes_extend (G : Graph k) (A : Observer k) (M : Bundle A)
    (V : Observation A) (x y : Node G A) (ts) :
    Realizes G A (extendBundle M V) x ts y ↔
      Realizes G A M x ts y ∧ ObservationAccepts G A V x ts y := by
  let V' : Observation M.machine := pullObservation (A := A) (M := M.machine) M.projection V
  constructor
  · rintro ⟨i,hi,j,hj,us,hix,hjy,ht,hr⟩
    have hinit := (sync_initial M.machine V' i).mp hi
    have hfinal := (sync_final M.machine V' j).mp hj
    have hs := trace_synchronize_sound (A := M.machine) (V := V') hr
    change M.projection (pairAt M.machine V' i).1 = x.2 at hix
    change M.projection (pairAt M.machine V' j).1 = y.2 at hjy
    have heq : mapTrace G M.projection (projectTrace M.machine V' G us) = ts := by
      exact (mapTrace_comp G M.projection (fun q => (pairAt M.machine V' q).1) us).trans ht
    have hp := observes_pull_sound M.projection V hs.2
    have hp' : ObservationAccepts G A V x ts y := by
      refine ⟨_,hinit.2,_,hfinal.2,?_⟩
      simpa [mapNode,projectNode,heq,hix,hjy] using hp
    refine ⟨?_,hp'⟩
    refine ⟨_,hinit.1,_,hfinal.1,projectTrace M.machine V' G us,hix,hjy,heq,?_⟩
    exact hs.1
  · rintro ⟨⟨i,hi,j,hj,us,hix,hjy,ht,hr⟩,a,ha,b,hb,hv⟩
    have hv' : Observes G M.machine V' (x.1,i) a us (y.1,j) b := by
      apply observes_pull_complete M.projection V hr
      simpa [mapNode,hix,hjy,ht] using hv
    obtain ⟨i',hi'⟩ := pair_represented M.machine V' i a
    obtain ⟨j',vs,hj',hproj,htr⟩ := trace_synchronize_complete hr a b hv' i' hi'
    refine ⟨i',?_,j',?_,vs,?_,?_,?_,htr⟩
    · apply (sync_initial M.machine V' i').mpr
      rw [hi']
      exact ⟨hi,ha⟩
    · apply (sync_final M.machine V' j').mpr
      rw [hj']
      exact ⟨hj,hb⟩
    · change M.projection (pairAt M.machine V' i').1 = x.2
      simpa [hi'] using hix
    · change M.projection (pairAt M.machine V' j').1 = y.2
      simpa [hj'] using hjy
    · change mapTrace G (fun q => M.projection (pairAt M.machine V' q).1) vs = ts
      rw [← mapTrace_comp G M.projection (fun q => (pairAt M.machine V' q).1) vs]
      change mapTrace G M.projection (projectTrace M.machine V' G vs) = ts
      rw [hproj,ht]

/-- Complete finite-family invariant at every exact base trace. -/
theorem realizes_bundle (G : Graph k) (A : Observer k) (Vs : List (Observation A))
    (x y : Node G A) (ts) :
    Realizes G A (bundle A Vs) x ts y ↔
    x.2 ∈ A.initial ∧ y.2 ∈ A.final ∧ TraceRun G A x ts y ∧
      ∀ V ∈ Vs, ObservationAccepts G A V x ts y := by
  induction Vs with
  | nil =>
    constructor
    · rintro ⟨i,hi,j,hj,us,hix,hjy,ht,hr⟩
      change i = x.2 at hix
      change j = y.2 at hjy
      have heq : us = ts := (mapTrace_id G A us).symm.trans ht
      subst i; subst j; subst us
      exact ⟨hi,hj,hr,by simp⟩
    · rintro ⟨hi,hj,hr,_⟩
      exact ⟨x.2,hi,y.2,hj,ts,rfl,rfl,mapTrace_id G A ts,hr⟩
  | cons V Vs ih =>
    rw [bundle,realizes_extend,ih]
    constructor
    · rintro ⟨⟨hi,hj,hr,hvs⟩,hv⟩
      refine ⟨hi,hj,hr,?_⟩
      intro W hw
      rcases List.mem_cons.mp hw with he | he
      · subst W; exact hv
      · exact hvs W he
    · rintro ⟨hi,hj,hr,hvs⟩
      exact ⟨⟨hi,hj,hr,fun W hw => hvs W (List.mem_cons_of_mem V hw)⟩,
        hvs V (List.mem_cons_self)⟩

/-- Arbitrarily many observers are realized by one generator trace. -/
theorem accepts_bundle_iff (G : Graph k) (A : Observer k) (Vs : List (Observation A))
    (u v : Fin G.size) :
    Accepts G (bundle A Vs).machine u v ↔
      ∃ q ∈ A.initial, ∃ p ∈ A.final, ∃ ts,
        TraceRun G A (u,q) ts (v,p) ∧
        ∀ V ∈ Vs, ObservationAccepts G A V (u,q) ts (v,p) := by
  constructor
  · rintro ⟨i,hi,j,hj,hr⟩
    obtain ⟨us,hu⟩ := run_exists_trace hr
    have hm : Realizes G A (bundle A Vs)
        (u,(bundle A Vs).projection i)
        (mapTrace G (bundle A Vs).projection us)
        (v,(bundle A Vs).projection j) := ⟨i,hi,j,hj,us,rfl,rfl,rfl,hu⟩
    have h := (realizes_bundle G A Vs _ _ _).mp hm
    exact ⟨_,h.1,_,h.2.1,_,h.2.2⟩
  · rintro ⟨q,hq,p,hp,ts,ht,hvs⟩
    obtain ⟨i,hi,j,hj,us,_,_,_,hr⟩ :=
      (realizes_bundle G A Vs (u,q) (v,p) ts).mpr ⟨hq,hp,ht,hvs⟩
    exact ⟨i,hi,j,hj,trace_to_run hr⟩

end RankQueryReconstruction
end Subtail

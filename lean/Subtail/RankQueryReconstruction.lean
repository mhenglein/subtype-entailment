import Subtail.RankQueryFirstReturn

/-!
# Shared generator traces for the reverse closure construction

Issue #29. An executable finite observer product retains the SAME generator
vertices, controls, and labels for all observations. It does not instantiate
ClosureFor. The missing diagram/portal compiler is not a hypothesis here.
-/
namespace Subtail
namespace RankQueryReconstruction
open RankQuery

/-- A step with its actual graph-edge label retained. -/
def TaggedStep (G : Graph k) (O : Observer k) (x : Node G O)
    (l : Label) (y : Node G O) : Prop :=
  G.edge x.1 l = some y.1 ∧
  y.2 ∈ O.move x.2 (G.colour x.1) l (G.colour y.1) ∧ Allowed G O y

/-- A concrete finite trace, not just an existential path. -/
inductive TraceRun (G : Graph k) (O : Observer k) :
    Node G O -> List (Label × Node G O) -> Node G O -> Prop where
  | nil {x} : Allowed G O x -> TraceRun G O x [] x
  | cons {x y z l ts} : Allowed G O x -> TaggedStep G O x l y ->
      TraceRun G O y ts z -> TraceRun G O x ((l,y)::ts) z

theorem trace_start {G : Graph k} {O : Observer k} {x y ts}
    (h : TraceRun G O x ts y) : Allowed G O x := by
  cases h with
  | nil hx => exact hx
  | cons hx _ _ => exact hx

theorem trace_append {G : Graph k} {O : Observer k} {x y z as bs}
    (ha : TraceRun G O x as y) (hb : TraceRun G O y bs z) :
    TraceRun G O x (as ++ bs) z := by
  induction ha generalizing z bs with
  | nil _ => exact hb
  | cons hx hs _ ih => exact .cons hx hs (ih hb)

theorem run_trans {G : Graph k} {O : Observer k} {x y z}
    (ha : Run G O x y) (hb : Run G O y z) : Run G O x z := by
  induction hb with
  | refl _ => exact ha
  | step _ hs ih => exact .step ih hs

theorem trace_to_run {G : Graph k} {O : Observer k} {x y ts}
    (h : TraceRun G O x ts y) : Run G O x y := by
  induction h with
  | nil hx => exact .refl hx
  | @cons x y z l ts hx hs ht ih =>
    exact run_trans (.step (.refl hx) ⟨l,hs⟩) ih

theorem run_exists_trace {G : Graph k} {O : Observer k} {x y}
    (h : Run G O x y) : ∃ ts, TraceRun G O x ts y := by
  induction h with
  | refl hx => exact ⟨[], .nil hx⟩
  | @step y z hy hs ih =>
    obtain ⟨ts,ht⟩ := ih
    obtain ⟨l,he,hm,ha⟩ := hs
    have hend : Allowed G O y := by
      induction hy with
      | refl h => exact h
      | step _ hs _ => exact hs.choose_spec.2.2
    exact ⟨ts ++ [(l,z)], trace_append ht (.cons hend ⟨he,hm,ha⟩ (.nil ha))⟩

/-- An observer of one generator. Colours and allowed output labels may depend
on the generator's controls, so synchronizing labels alone is NOT enough. -/
structure Observation (A : Observer k) where
  observer : Observer k
  colour : Fin A.size -> Colour k -> Colour k
  labels : Fin A.size -> Colour k -> Label -> Colour k -> Fin A.size -> List Label

/-- Observe a FIXED generator trace. Local output-label choices (e.g. S or K_b)
may differ between observers; the generator trace cannot. -/
inductive Observes (G : Graph k) (A : Observer k) (V : Observation A) :
    Node G A -> Fin V.observer.size -> List (Label × Node G A) ->
    Node G A -> Fin V.observer.size -> Prop where
  | nil {x q} : V.observer.allows q (V.colour x.2 (G.colour x.1)) = true ->
      Observes G A V x q [] x q
  | cons {x y z q r s l ts} :
      V.observer.allows q (V.colour x.2 (G.colour x.1)) = true ->
      (∃ a ∈ V.labels x.2 (G.colour x.1) l (G.colour y.1) y.2,
        r ∈ V.observer.move q (V.colour x.2 (G.colour x.1)) a
          (V.colour y.2 (G.colour y.1))) ->
      Observes G A V y r ts z s -> Observes G A V x q ((l,y)::ts) z s

theorem observes_start {G : Graph k} {A : Observer k} {V : Observation A}
    {x y q p ts} (h : Observes G A V x q ts y p) :
    V.observer.allows q (V.colour x.2 (G.colour x.1)) = true := by
  cases h with
  | nil hx => exact hx
  | cons hx _ _ => exact hx

theorem observes_append {G : Graph k} {A : Observer k} {V : Observation A}
    {x y z p q r as bs} (ha : Observes G A V x p as y q)
    (hb : Observes G A V y q bs z r) :
    Observes G A V x p (as ++ bs) z r := by
  induction ha generalizing z r bs with
  | nil _ => exact hb
  | cons hx hs _ ih => exact .cons hx hs (ih hb)

/-- Explicit finite control enumeration, including zero-control observers. -/
def pairs (A : Observer k) (V : Observation A) :
    List (Fin A.size × Fin V.observer.size) :=
  (List.finRange A.size).flatMap fun p =>
    (List.finRange V.observer.size).map fun q => (p,q)

def pairAt (A : Observer k) (V : Observation A) (i : Fin (pairs A V).length) :
    Fin A.size × Fin V.observer.size := (pairs A V).get i

theorem pair_represented (A : Observer k) (V : Observation A)
    (p : Fin A.size) (q : Fin V.observer.size) :
    ∃ i, pairAt A V i = (p,q) := by
  apply List.mem_iff_get.mp
  exact List.mem_flatMap.mpr ⟨p,List.mem_finRange _,
    List.mem_map.mpr ⟨q,List.mem_finRange _,rfl⟩⟩

/-- Executable product on the original RankQuery.Observer type. -/
def synchronize (A : Observer k) (V : Observation A) : Observer k where
  size := (pairs A V).length
  initial := (List.finRange (pairs A V).length).filter fun i =>
    decide ((pairAt A V i).1 ∈ A.initial) &&
    decide ((pairAt A V i).2 ∈ V.observer.initial)
  final := (List.finRange (pairs A V).length).filter fun i =>
    decide ((pairAt A V i).1 ∈ A.final) &&
    decide ((pairAt A V i).2 ∈ V.observer.final)
  allows := fun i c => A.allows (pairAt A V i).1 c &&
    V.observer.allows (pairAt A V i).2 (V.colour (pairAt A V i).1 c)
  move := fun i c l d => (List.finRange (pairs A V).length).filter fun j =>
    decide ((pairAt A V j).1 ∈ A.move (pairAt A V i).1 c l d) &&
    (V.labels (pairAt A V i).1 c l d (pairAt A V j).1).any fun a =>
      decide ((pairAt A V j).2 ∈ V.observer.move (pairAt A V i).2
        (V.colour (pairAt A V i).1 c) a (V.colour (pairAt A V j).1 d))

theorem sync_initial (A : Observer k) (V : Observation A) (i) :
    i ∈ (synchronize A V).initial ↔
    (pairAt A V i).1 ∈ A.initial ∧ (pairAt A V i).2 ∈ V.observer.initial := by
  simp [synchronize, List.mem_filter, Bool.and_eq_true]

theorem sync_final (A : Observer k) (V : Observation A) (i) :
    i ∈ (synchronize A V).final ↔
    (pairAt A V i).1 ∈ A.final ∧ (pairAt A V i).2 ∈ V.observer.final := by
  simp [synchronize, List.mem_filter, Bool.and_eq_true]

theorem sync_allowed (G : Graph k) (A : Observer k) (V : Observation A) (x) :
    Allowed G (synchronize A V) x ↔
    Allowed G A (x.1,(pairAt A V x.2).1) ∧
    V.observer.allows (pairAt A V x.2).2
      (V.colour (pairAt A V x.2).1 (G.colour x.1)) = true := by
  simp [Allowed, synchronize, Bool.and_eq_true]

theorem sync_move (A : Observer k) (V : Observation A) (i j c l d) :
    j ∈ (synchronize A V).move i c l d ↔
    (pairAt A V j).1 ∈ A.move (pairAt A V i).1 c l d ∧
    ∃ a ∈ V.labels (pairAt A V i).1 c l d (pairAt A V j).1,
      (pairAt A V j).2 ∈ V.observer.move (pairAt A V i).2
        (V.colour (pairAt A V i).1 c) a (V.colour (pairAt A V j).1 d) := by
  simp [synchronize, List.mem_filter, Bool.and_eq_true, List.any_eq_true]

def projectNode (A : Observer k) (V : Observation A) (G : Graph k)
    (x : Node G (synchronize A V)) : Node G A :=
  (x.1,(pairAt A V x.2).1)

def projectTrace (A : Observer k) (V : Observation A) (G : Graph k)
    (ts : List (Label × Node G (synchronize A V))) : List (Label × Node G A) :=
  ts.map fun t => (t.1,projectNode A V G t.2)

/-- Every accepted product trace has one generator trace observed consistently. -/
theorem trace_synchronize_sound {G : Graph k} {A : Observer k} {V : Observation A}
    {x y ts} (h : TraceRun G (synchronize A V) x ts y) :
    TraceRun G A (projectNode A V G x) (projectTrace A V G ts) (projectNode A V G y) ∧
    Observes G A V (projectNode A V G x) (pairAt A V x.2).2
      (projectTrace A V G ts) (projectNode A V G y) (pairAt A V y.2).2 := by
  induction h with
  | nil hx =>
    have hh := (sync_allowed G A V _).mp hx
    exact ⟨.nil hh.1,.nil hh.2⟩
  | @cons x y z l ts hx hs ht ih =>
    have hh := (sync_allowed G A V _).mp hx
    have hy := (sync_allowed G A V _).mp hs.2.2
    have hm := (sync_move A V _ _ _ _ _).mp hs.2.1
    exact ⟨.cons hh.1 ⟨hs.1,hm.1,hy.1⟩ ih.1,
      .cons hh.2 hm.2 ih.2⟩

/-- Conversely the finite product realizes every genuinely shared trace.
No path length, reference length, or deterministic observer premise is used. -/
theorem trace_synchronize_complete {G : Graph k} {A : Observer k} {V : Observation A}
    {x y ts} (h : TraceRun G A x ts y) :
    ∀ q p, Observes G A V x q ts y p ->
    ∀ i, pairAt A V i = (x.2,q) ->
    ∃ j us, pairAt A V j = (y.2,p) ∧
      projectTrace A V G us = ts ∧
      TraceRun G (synchronize A V) (x.1,i) us (y.1,j) := by
  induction h with
  | nil hx =>
    intro q p hv i hi
    cases hv with
    | nil hq =>
      refine ⟨i,[],hi,rfl,.nil ?_⟩
      apply (sync_allowed G A V _).mpr
      simpa [hi] using And.intro hx hq
  | @cons x y z l ts hx hs ht ih =>
    intro q p hv i hi
    cases hv with
    | @cons _ _ _ _ r _ _ _ hq hv ht' =>
      obtain ⟨j,hj⟩ := pair_represented A V y.2 r
      obtain ⟨j',us,hj',hus,hrun⟩ := ih r p ht' j hj
      refine ⟨j',(l,(y.1,j))::us,hj',?_,.cons ?_ ?_ hrun⟩
      · simp [projectTrace,projectNode,hj,hus]
      · apply (sync_allowed G A V _).mpr
        simpa [hi] using And.intro hx hq
      · refine ⟨hs.1,?_,?_⟩
        · apply (sync_move A V _ _ _ _ _).mpr
          simpa [hi,hj] using And.intro hs.2.1 hv
        · exact trace_start hrun

/-- Exact existential semantics: the generator trace is quantified ONCE. -/
theorem accepts_synchronize_iff (G : Graph k) (A : Observer k) (V : Observation A)
    (u v : Fin G.size) :
    Accepts G (synchronize A V) u v ↔
    ∃ q ∈ A.initial, ∃ p ∈ A.final,
    ∃ a ∈ V.observer.initial, ∃ b ∈ V.observer.final, ∃ ts,
      TraceRun G A (u,q) ts (v,p) ∧ Observes G A V (u,q) a ts (v,p) b := by
  constructor
  · rintro ⟨i,hi,j,hj,hr⟩
    obtain ⟨ts,ht⟩ := run_exists_trace hr
    have hs := trace_synchronize_sound ht
    have hinit := (sync_initial A V i).mp hi
    have hfinal := (sync_final A V j).mp hj
    exact ⟨_,hinit.1,_,hfinal.1,_,hinit.2,_,hfinal.2,_,hs⟩
  · rintro ⟨q,hq,p,hp,a,ha,b,hb,ts,ht,hv⟩
    obtain ⟨i,hi⟩ := pair_represented A V q a
    obtain ⟨j,us,hj,_,hu⟩ := trace_synchronize_complete ht a b hv i hi
    refine ⟨i,?_,j,?_,trace_to_run hu⟩
    · apply (sync_initial A V i).mpr
      simpa [hi] using And.intro hq ha
    · apply (sync_final A V j).mpr
      simpa [hj] using And.intro hp hb

end RankQueryReconstruction
end Subtail

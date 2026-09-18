import Subtail.RankQuerySound

/-!
# Portal-edge transport helpers for rank-query reconstruction

Disjoint support for A018 stage 4c (issue #29). These graph-independent
lemmas turn the compiler's Boolean portal contracts into literal observer
steps/runs once the reconstructed extension supplies the corresponding edge
and mapped endpoint colours.

They do not assume or prove the Closure Lemma.
-/
namespace Subtail
namespace RankQueryPortalTransport

open RankQuery RankQueryCompiler

variable {k : Nat}

/-- portalMove is exactly membership of the requested target control in the
original observer's transition list on the mapped endpoint colours. -/
theorem portalMove_mem (P : Portal k) (c d : Colour k)
    (h : portalMove P c d = true) :
    P.dst ∈ P.observer.move P.src (P.left c) P.label (P.right d) := by
  unfold portalMove at h
  exact List.contains_iff_mem.mp h

/-- portalTest packages source/target permission and the semantic move on one
old-origin colour. -/
theorem portalTest_facts (P : Portal k) (c : Colour k)
    (h : portalTest P c = true) :
    P.observer.allows P.src (P.left c) = true ∧
    P.observer.allows P.dst (P.right c) = true ∧
    P.dst ∈ P.observer.move P.src (P.left c) P.label (P.right c) := by
  unfold portalTest at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, List.contains_iff_mem.mp h.2⟩

/-- A successful one-colour portal test becomes a real observer step whenever
the reconstructed graph has the advertised edge and mapped endpoint colours. -/
theorem portalTest_step {G : Graph k} (P : Portal k) (c : Colour k)
    {u v : Fin G.size}
    (h : portalTest P c = true)
    (hedge : G.edge u P.label = some v)
    (hsrc : G.colour u = P.left c)
    (hdst : G.colour v = P.right c) :
    Step G P.observer (u, P.src) (v, P.dst) := by
  obtain ⟨hs, ht, hm⟩ := portalTest_facts P c h
  refine ⟨P.label, hedge, ?_, ?_⟩
  · simpa [hsrc, hdst] using hm
  · show P.observer.allows P.dst (G.colour v) = true
    simpa [hdst] using ht

/-- Same contract as portalTest_step, promoted to a one-edge run. -/
theorem portalTest_run {G : Graph k} (P : Portal k) (c : Colour k)
    {u v : Fin G.size}
    (h : portalTest P c = true)
    (hedge : G.edge u P.label = some v)
    (hsrc : G.colour u = P.left c)
    (hdst : G.colour v = P.right c) :
    Run G P.observer (u, P.src) (v, P.dst) := by
  have hs := (portalTest_facts P c h).1
  refine Run.step (Run.refl ?_) (portalTest_step P c h hedge hsrc hdst)
  show P.observer.allows P.src (G.colour u) = true
  simpa [hsrc] using hs

/-- The two-colour portalMove form used by a fresh-to-core K exit becomes a
literal step once separately compiled endpoint tests establish permission. -/
theorem portalMove_step {G : Graph k} (P : Portal k) (c d : Colour k)
    {u v : Fin G.size}
    (hm : portalMove P c d = true)
    (ht : P.observer.allows P.dst (P.right d) = true)
    (hedge : G.edge u P.label = some v)
    (hsrc : G.colour u = P.left c)
    (hdst : G.colour v = P.right d) :
    Step G P.observer (u, P.src) (v, P.dst) := by
  refine ⟨P.label, hedge, ?_, ?_⟩
  · simpa [hsrc, hdst] using portalMove_mem P c d hm
  · show P.observer.allows P.dst (G.colour v) = true
    simpa [hdst] using ht

/-- With source permission as well, a portalMove gives the full one-edge run
used when gluing a K-exit to adjacent reconstructed pieces. -/
theorem portalMove_run {G : Graph k} (P : Portal k) (c d : Colour k)
    {u v : Fin G.size}
    (hm : portalMove P c d = true)
    (hs : P.observer.allows P.src (P.left c) = true)
    (ht : P.observer.allows P.dst (P.right d) = true)
    (hedge : G.edge u P.label = some v)
    (hsrc : G.colour u = P.left c)
    (hdst : G.colour v = P.right d) :
    Run G P.observer (u, P.src) (v, P.dst) := by
  refine Run.step (Run.refl ?_) (portalMove_step P c d hm ht hedge hsrc hdst)
  show P.observer.allows P.src (G.colour u) = true
  simpa [hsrc] using hs

end RankQueryPortalTransport
end Subtail

import Subtail.RankQuerySound

/-!
# Finite enumeration of bounded compiler diagrams (#28)

This module enumerates the existing `RankQueryCompiler.Diagram` syntax.
It does not postulate that every satisfying extension has such a diagram.
The syntactic membership theorem and the inherited reconstruction theorem
are separate from that remaining semantic extraction obligation.

All bounds concern finite diagram data, never reference or witness length.
No existing compiler, graph or query definition is changed.
-/
namespace Subtail
namespace RankQueryEnumeration
open RankQuery RankQueryCompiler

/-! ## Finite list products -/

def exactLists (xs : List a) : Nat -> List (List a)
  | 0 => [[]]
  | n + 1 => xs.flatMap fun x => (exactLists xs n).map (x :: .)

theorem mem_exactLists (xs : List a) (n : Nat) (ys : List a) :
    ys ∈ exactLists xs n <->
      ys.length = n ∧ ∀ y ∈ ys, y ∈ xs := by
  induction n generalizing ys with
  | zero => cases ys <;> simp [exactLists]
  | succ n ih =>
    cases ys with
    | nil => simp [exactLists]
    | cons y ys =>
      simp only [exactLists, List.mem_flatMap, List.mem_map]
      constructor
      . rintro ⟨x, hx, zs, hz, he⟩
        have hxy := (List.cons.inj he).1
        have hzys := (List.cons.inj he).2
        subst x
        subst zs
        obtain ⟨ hl, ha ⟩ := (ih ys).mp hz
        refine ⟨ by simp [hl], ?_ ⟩
        intro v hv
        rcases List.mem_cons.mp hv with he | hm
        . subst v; exact hx
        . exact ha v hm
      . rintro ⟨ hl, ha ⟩
        refine ⟨y, ha y (by simp), ys, ?_, rfl⟩
        apply (ih ys).mpr
        refine ⟨by simpa using hl, ?_⟩
        intro v hv
        exact ha v (by simp [hv])

def boundedLists (xs : List a) (n : Nat) : List (List a) :=
  (List.range (n + 1)).flatMap (exactLists xs)

theorem mem_boundedLists (xs : List a) (n : Nat) (ys : List a) :
    ys ∈ boundedLists xs n <->
      ys.length <= n ∧ ∀ y ∈ ys, y ∈ xs := by
  simp only [boundedLists, List.mem_flatMap, List.mem_range, mem_exactLists]
  constructor
  . rintro ⟨i, hi, he, ha⟩
    subst i
    exact ⟨by omega, ha⟩
  . rintro ⟨hl, ha⟩
    exact ⟨ys.length, by omega, rfl, ha⟩

def bools : List Bool := [false, true]

theorem mem_bools (b : Bool) : b ∈ bools := by
  cases b <;> simp [bools]

def nexts : List (Option Bool) := [none, some false, some true]

theorem mem_nexts (b : Option Bool) : b ∈ nexts := by
  cases b with
  | none => simp [nexts]
  | some b => cases b <;> simp [nexts]

/-- This conversion retains a proof of the exact length. -/
def vectorFromList (n : Nat) (xs : List a) : Option (Vector a n) :=
  if h : xs.length = n then some ⟨xs.toArray, by simpa using h⟩ else none

theorem vectorFromList_toList (v : Vector a n) :
    vectorFromList n v.toList = some v := by
  cases v with
  | mk ar h => simp [vectorFromList, Vector.toList, h]

def masks (k : Nat) : List (Vector Bool k) :=
  (exactLists bools k).filterMap (vectorFromList k)

theorem mem_masks (v : Vector Bool k) : v ∈ masks k := by
  apply List.mem_filterMap.mpr
  refine ⟨v.toList, ?_, vectorFromList_toList v⟩
  apply (mem_exactLists _ _ _).mpr
  constructor
  . cases v with
    | mk ar h => simpa [Vector.toList] using h
  . intro b _
    exact mem_bools b

def colours (k : Nat) : List (Colour k) :=
  (List.finRange k).flatMap fun q =>
  (masks k).flatMap fun m =>
  nexts.flatMap fun nxt =>
  bools.flatMap fun root =>
  bools.map fun last => ⟨q, m, nxt, root, last⟩

theorem mem_colours (c : Colour k) : c ∈ colours k := by
  cases c with
  | mk q m nxt root last =>
    simp [colours, List.mem_flatMap, mem_masks, mem_nexts, mem_bools]

/-! ## Independent structural specifications for finite fields -/

def locBound (core groups : Nat) : Loc -> Prop
  | .core i => i < core
  | .fresh i => i < groups

def locations (core groups : Nat) : List Loc :=
  (List.range core).map Loc.core ++ (List.range groups).map Loc.fresh

theorem mem_locations (core groups : Nat) (x : Loc) :
    x ∈ locations core groups <-> locBound core groups x := by
  cases x <;> simp [locations, locBound]

def kinds : List PieceKind := [.core, .forward, .enter, .exit, .wrap]

theorem mem_kinds (t : PieceKind) : t ∈ kinds := by
  cases t <;> simp [kinds]

/-- A deliberately redundant envelope; kind-specific restrictions stay in the
existing Boolean `pieceValid`. -/
def pieceBound (n : Nat) (p : Piece) : Prop :=
  p.source < n ∧ p.target < n ∧ p.lc < n ∧ p.rc < n

def pieces (n : Nat) : List Piece :=
  kinds.flatMap fun t =>
  (List.range n).flatMap fun s =>
  (List.range n).flatMap fun d =>
  (List.range n).flatMap fun lc =>
  (List.range n).flatMap fun rc =>
  labels.map fun l => ⟨t, s, d, lc, rc, l⟩

theorem mem_pieces (n : Nat) (p : Piece) :
    p ∈ pieces n <-> pieceBound n p := by
  unfold pieces
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  . rintro ⟨t, _, s, hs, d, hd, lc, hlc, rc, hrc, l, _, he⟩
    subst p
    exact ⟨List.mem_range.mp hs, List.mem_range.mp hd,
      List.mem_range.mp hlc, List.mem_range.mp hrc⟩
  . rintro ⟨hs, hd, hlc, hrc⟩
    exact ⟨p.kind, mem_kinds _, p.source, List.mem_range.mpr hs,
      p.target, List.mem_range.mpr hd, p.lc, List.mem_range.mpr hlc,
      p.rc, List.mem_range.mpr hrc, p.label, mem_labels _, rfl⟩

abbrev Seam := Nat × Nat × Nat × Nat

def seamBound (n : Nat) (s : Seam) : Prop :=
  s.1 < n ∧ s.2.1 < n ∧ s.2.2.1 < n ∧ s.2.2.2 < n

def seams (n : Nat) : List Seam :=
  (List.range n).flatMap fun ai =>
  (List.range n).flatMap fun pi =>
  (List.range n).flatMap fun g =>
  (List.range n).map fun q => (ai, pi, g, q)

theorem mem_seams (n : Nat) (s : Seam) :
    s ∈ seams n <-> seamBound n s := by
  unfold seams
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  . rintro ⟨ai, ha, pi, hp, g, hg, q, hq, he⟩
    subst s
    exact ⟨List.mem_range.mp ha, List.mem_range.mp hp,
      List.mem_range.mp hg, List.mem_range.mp hq⟩
  . rintro ⟨ha, hp, hg, hq⟩
    exact ⟨s.1, List.mem_range.mpr ha, s.2.1, List.mem_range.mpr hp,
      s.2.2.1, List.mem_range.mpr hg, s.2.2.2, List.mem_range.mpr hq, rfl⟩

/-- Separate caps avoid confusing reference length with a syntax budget.
`scalar` is an exclusive bound on piece fields and the four seam coordinates;
the other four bounds are inclusive. -/
structure Limits where
  groups : Nat
  core : Nat
  perAtom : Nat
  seamEntries : Nat
  scalar : Nat
  deriving Repr

/-- Structural, graph-independent boundedness. This does not include
`validDiagram`, satisfaction, or membership in the enumerator. -/
def Bounded (c : Clause k) (b : Limits) (D : Diagram k) : Prop :=
  0 < D.groups ∧ D.groups <= b.groups ∧ D.coreVars <= b.core ∧
  D.loc.length = c.vars ∧ (∀ x ∈ D.loc, locBound D.coreVars D.groups x) ∧
  D.states.length = D.groups ∧ D.nextBits.length = D.groups ∧
  D.pieces.length = c.atoms.length ∧
  (∀ ps ∈ D.pieces, ps.length <= b.perAtom ∧
    ∀ p ∈ ps, pieceBound b.scalar p) ∧
  D.seams.length <= b.seamEntries ∧
  (∀ s ∈ D.seams, seamBound b.scalar s)

/-- Total finite enumeration. The product is intentionally redundant so that
its completeness can be proved without any heuristic normalization.
No word, reference graph, stack, solver oracle or semantic predicate is read. -/
def diagrams (c : Clause k) (b : Limits) : List (Diagram k) :=
  (List.range (b.groups + 1)).flatMap fun ng =>
  if ng = 0 then [] else
    (List.range (b.core + 1)).flatMap fun nc =>
    (exactLists (locations nc ng) c.vars).flatMap fun loc =>
    (exactLists (List.finRange k) ng).flatMap fun states =>
    (exactLists nexts ng).flatMap fun nxt =>
    bools.flatMap fun first =>
    (colours k).flatMap fun old =>
    (exactLists (boundedLists (pieces b.scalar) b.perAtom) c.atoms.length).flatMap fun paths =>
    (boundedLists (seams b.scalar) b.seamEntries).map fun joins =>
    ⟨ng, nc, loc, states, nxt, first, old, paths, joins⟩

/-- Exact syntactic completeness, with all bounds on the right independent of
the definition of `diagrams`. -/
theorem mem_diagrams (c : Clause k) (b : Limits) (D : Diagram k) :
    D ∈ diagrams c b <-> Bounded c b D := by
  constructor
  . intro h
    unfold diagrams at h
    obtain ⟨ng, hng, h⟩ := List.mem_flatMap.mp h
    by_cases hz : ng = 0
    . simp [hz] at h
    . rw [if_neg hz] at h
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨nc, hnc, loc, hlo, states, hs, nxt, hn,
        first, _, old, _, paths, hp, joins, hj, he⟩ := h
      subst D
      obtain ⟨hloLen, hloAll⟩ := (mem_exactLists _ _ _).mp hlo
      obtain ⟨hsLen, _⟩ := (mem_exactLists _ _ _).mp hs
      obtain ⟨hnLen, _⟩ := (mem_exactLists _ _ _).mp hn
      obtain ⟨hpLen, hpAll⟩ := (mem_exactLists _ _ _).mp hp
      obtain ⟨hjLen, hjAll⟩ := (mem_boundedLists _ _ _).mp hj
      dsimp only [Bounded]
      refine ⟨by omega, by have := List.mem_range.mp hng; omega,
        by have := List.mem_range.mp hnc; omega, hloLen, ?_, hsLen, hnLen,
        hpLen, ?_, hjLen, ?_⟩
      . intro x hx
        exact (mem_locations _ _ _).mp (hloAll x hx)
      . intro ps hps
        obtain ⟨hlen, hall⟩ := (mem_boundedLists _ _ _).mp (hpAll ps hps)
        exact ⟨hlen, fun p hp => (mem_pieces _ _).mp (hall p hp)⟩
      . intro x hx
        exact (mem_seams _ _).mp (hjAll x hx)
  . rintro ⟨hpos, hng, hnc, hloLen, hloAll, hsLen, hnLen,
      hpLen, hpAll, hjLen, hjAll⟩
    unfold diagrams
    apply List.mem_flatMap.mpr
    refine ⟨D.groups, List.mem_range.mpr (by omega), ?_⟩
    rw [if_neg (by omega : D.groups ≠ 0)]
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨D.coreVars, List.mem_range.mpr (by omega),
      D.loc, ?_, D.states, ?_, D.nextBits, ?_, D.firstBit, mem_bools _,
      D.oldEnd, mem_colours _, D.pieces, ?_, D.seams, ?_, ?_⟩
    . apply (mem_exactLists _ _ _).mpr
      exact ⟨hloLen, fun x hx => (mem_locations _ _ _).mpr (hloAll x hx)⟩
    . apply (mem_exactLists _ _ _).mpr
      exact ⟨hsLen, by intros; simp⟩
    . apply (mem_exactLists _ _ _).mpr
      exact ⟨hnLen, fun x _ => mem_nexts x⟩
    . apply (mem_exactLists _ _ _).mpr
      refine ⟨hpLen, ?_⟩
      intro ps hps
      obtain ⟨hlen, hall⟩ := hpAll ps hps
      apply (mem_boundedLists _ _ _).mpr
      exact ⟨hlen, fun p hp => (mem_pieces _ _).mpr (hall p hp)⟩
    . apply (mem_boundedLists _ _ _).mpr
      exact ⟨hjLen, fun x hx => (mem_seams _ _).mpr (hjAll x hx)⟩
    . rfl

/-- Filter only by the already proved compiler's syntactic guard. -/
def validDiagrams (I : Instance k) (c : Clause k) (b : Limits) : List (Diagram k) :=
  (diagrams c b).filter (validDiagram I c)

theorem mem_validDiagrams (I : Instance k) (c : Clause k) (b : Limits) (D : Diagram k) :
    D ∈ validDiagrams I c b <-> Bounded c b D ∧ validDiagram I c D = true := by
  simp [validDiagrams, mem_diagrams]

/-- The clause preimage now has a finite executable enumeration, not a supplied
list of diagrams. The supplied *syntax* limits are still explicit. -/
def preimageClause (I : Instance k) (c : Clause k) (b : Limits) : Query k :=
  preimageOver I c (diagrams c b)

/-- A finite full-query compiler for any computable per-clause budget. -/
def preimage (I : Instance k) (budget : Clause k -> Limits) (phi : Query k) : Query k :=
  phi.flatMap fun c => preimageClause I c (budget c)

/-- Membership is exact even though clauses contain functions and need not
carry a decidable structural equality. -/
theorem mem_preimageClause (I : Instance k) (c : Clause k) (b : Limits) (P : Clause k) :
    P ∈ preimageClause I c b <->
    ∃ D, Bounded c b D ∧ compileDiagram I c D = some P := by
  simp [preimageClause, preimageOver, List.mem_filterMap, mem_diagrams]

/-- Precise remaining forward obligation: extraction of a bounded diagram,
not a second assumed preimage-correctness axiom. -/
def DiagramCoverage (I : Instance k) (budget : Clause k -> Limits) : Prop :=
  ∀ B C, SafeReference I B -> FirstReturnExt I B C ->
    ∀ c, SatClause (prefixGraph I C) c ->
      ∃ D, Bounded c (budget c) D ∧
        validDiagram I c D = true ∧
        SatClause (prefixGraph I B) (compileValid I c D)

/-- No base model introduced by this concrete enumeration is spurious.
This applies to any syntax limits, independently of coverage. -/
theorem preimage_sound (I : Instance k) (budget : Clause k -> Limits)
    (phi : Query k) (B : Reference k) (hB : SafeReference I B)
    (h : Sat (prefixGraph I B) (preimage I budget phi)) :
    ∃ C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) phi := by
  exact RankQuerySound.closure_reverse I (fun c => diagrams c (budget c)) phi B hB h

/-- Exact meaning of a bounded clause search, on any finite query graph. -/
theorem sat_preimageClause_iff (I : Instance k) (G : Graph k)
    (c : Clause k) (b : Limits) :
    Sat G (preimageClause I c b) <->
    ∃ D, Bounded c b D ∧ validDiagram I c D = true ∧
      SatClause G (compileValid I c D) := by
  constructor
  . rintro ⟨P, hP, hsat⟩
    obtain ⟨D, hD, hc⟩ := (mem_preimageClause I c b P).mp hP
    unfold compileDiagram at hc
    split at hc
    next hv =>
      have hp := Option.some.inj hc
      subst P
      exact ⟨D, hD, hv, hsat⟩
    next hv => contradiction
  . rintro ⟨D, hD, hv, hsat⟩
    refine ⟨compileValid I c D, ?_, hsat⟩
    apply (mem_preimageClause I c b _).mpr
    exact ⟨D, hD, by simp [compileDiagram, hv]⟩

/-- This explicitly exposes the only semantic obligation not discharged by
finite syntactic enumeration. It does not assume it implicitly. -/
theorem forward_of_coverage (I : Instance k) (budget : Clause k -> Limits)
    (coverage : DiagramCoverage I budget) (B C : Reference k)
    (hB : SafeReference I B) (hC : FirstReturnExt I B C)
    (phi : Query k) (hsat : Sat (prefixGraph I C) phi) :
    Sat (prefixGraph I B) (preimage I budget phi) := by
  obtain ⟨c, hc, hm⟩ := hsat
  obtain ⟨D, hd, hv, hp⟩ := coverage B C hB hC c hm
  refine ⟨compileValid I c D, ?_, hp⟩
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  apply (mem_preimageClause I c (budget c) _).mpr
  exact ⟨D, hd, by simp [compileDiagram, hv]⟩

/-- Both directions follow after actual bounded-diagram extraction is proved.
This theorem proves no weight bound and assumes its coverage argument. -/
theorem preimage_iff_of_coverage (I : Instance k) (budget : Clause k -> Limits)
    (coverage : DiagramCoverage I budget) (B : Reference k)
    (hB : SafeReference I B) (phi : Query k) :
    Sat (prefixGraph I B) (preimage I budget phi) <->
    ∃ C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) phi := by
  constructor
  . exact preimage_sound I budget phi B hB
  . rintro ⟨C, hC, hs⟩
    exact forward_of_coverage I budget coverage B C hB hC phi hs

end RankQueryEnumeration
end Subtail

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
      ys.length = n ∧ forall y ∈ ys, y ∈ xs := by
  induction n generalizing ys with
  | zero => simp [exactLists]
  | succ n ih =>
    cases ys with
    | nil => simp [exactLists]
    | cons y ys =>
      simp [exactLists, List.mem_flatMap, ih, Nat.succ_eq_add_one, and_assoc]

def boundedLists (xs : List a) (n : Nat) : List (List a) :=
  (List.range (n + 1)).flatMap (exactLists xs)

theorem mem_boundedLists (xs : List a) (n : Nat) (ys : List a) :
    ys ∈ boundedLists xs n <->
      ys.length <= n ∧ forall y ∈ ys, y ∈ xs := by
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

def colours (k : Nat) : List (Colour k) := do
  let q <- List.finRange k
  let m <- masks k
  let nxt <- nexts
  let root <- bools
  let last <- bools
  pure ⟨q, m, nxt, root, last⟩

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

def pieces (n : Nat) : List Piece := do
  let t <- kinds
  let s <- List.range n
  let d <- List.range n
  let lc <- List.range n
  let rc <- List.range n
  let l <- labels
  pure ⟨t, s, d, lc, rc, l⟩

theorem mem_pieces (n : Nat) (p : Piece) :
    p ∈ pieces n <-> pieceBound n p := by
  cases p with
  | mk t s d lc rc l =>
    simp [pieces, pieceBound, List.mem_flatMap, mem_kinds, mem_labels, and_assoc]

abbrev Seam := Nat × Nat × Nat × Nat

def seamBound (n : Nat) (s : Seam) : Prop :=
  s.1 < n ∧ s.2.1 < n ∧ s.2.2.1 < n ∧ s.2.2.2 < n

def seams (n : Nat) : List Seam := do
  let ai <- List.range n
  let pi <- List.range n
  let g <- List.range n
  let q <- List.range n
  pure (ai, pi, g, q)

theorem mem_seams (n : Nat) (s : Seam) :
    s ∈ seams n <-> seamBound n s := by
  rcases s with ⟨ai, pi, g, q⟩
  simp [seams, seamBound, List.mem_flatMap, and_assoc]

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
  D.loc.length = c.vars ∧ (forall x ∈ D.loc, locBound D.coreVars D.groups x) ∧
  D.states.length = D.groups ∧ D.nextBits.length = D.groups ∧
  D.pieces.length = c.atoms.length ∧
  (forall ps ∈ D.pieces, ps.length <= b.perAtom ∧
    forall p ∈ ps, pieceBound b.scalar p) ∧
  D.seams.length <= b.seamEntries ∧
  (forall s ∈ D.seams, seamBound b.scalar s)

/-- Total finite enumeration. The product is intentionally redundant so that
its completeness can be proved without any heuristic normalization.
No word, reference graph, stack, solver oracle or semantic predicate is read. -/
def diagrams (c : Clause k) (b : Limits) : List (Diagram k) := do
  let ng <- List.range (b.groups + 1)
  if ng = 0 then [] else do
    let nc <- List.range (b.core + 1)
    let loc <- exactLists (locations nc ng) c.vars
    let states <- exactLists (List.finRange k) ng
    let nxt <- exactLists nexts ng
    let first <- bools
    let old <- colours k
    let paths <- exactLists (boundedLists (pieces b.scalar) b.perAtom) c.atoms.length
    let joins <- boundedLists (seams b.scalar) b.seamEntries
    pure ⟨ng, nc, loc, states, nxt, first, old, paths, joins⟩

/-- Exact syntactic completeness, with all bounds on the right independent of
the definition of `diagrams`. -/
theorem mem_diagrams (c : Clause k) (b : Limits) (D : Diagram k) :
    D ∈ diagrams c b <-> Bounded c b D := by
  cases D with
  | mk ng nc loc states nxt first old paths joins =>
    simp [diagrams, Bounded, List.mem_flatMap, mem_exactLists,
      mem_boundedLists, mem_locations, mem_pieces, mem_seams,
      mem_nexts, mem_bools, mem_colours, and_assoc, Nat.lt_succ_iff,
      Nat.pos_iff_ne_zero]

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
  forall B C, SafeReference I B -> FirstReturnExt I B C ->
    forall c, SatClause (prefixGraph I C) c ->
      ∃ D, Bounded c (budget c) D ∧
        validDiagram I c D = true ∧
        SatClause (prefixGraph I B) (compileValid I c D)

end RankQueryEnumeration
end Subtail

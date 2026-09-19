import Subtail.InfiniteWitness

/-!
# Concrete finite-prefix and repeated-cycle streams

This module fixes the stream interface used by the C029 reverse monitor.  A
finite prefix is followed by a (possibly non-primitive) cyclic word.  The
definitions are total on all words; the theorems which use a period assume
that the cycle is nonempty.
-/

namespace Subtail
namespace PeriodicRun

open AbsorbingTerminal
open InfiniteWitness

variable {k : Nat}

/-- The infinite stream obtained by repeating `c`.  The empty word is mapped
to the constant false stream only to keep this definition total; all period
lemmas require `c ≠ []`. -/
def periodicStream (c : Word) (t : Nat) : Bool :=
  (c[t % c.length]?).getD false

/-- The stream obtained by reading `w` and then repeating `c`. -/
def prefixStream (w c : Word) (t : Nat) : Bool :=
  if t < w.length then (w[t]?).getD false
  else periodicStream c (t - w.length)

/-- The monitor's semantic acceptance predicate for an old prefix. -/
def PrefixGood (I : Instance k) (w c : Word) : Prop :=
  ∀ i j, i < j → j ≤ w.length →
    PeriodicTail.SameSuffix (prefixStream w c) i j →
      unflaggedCheck I (stateAt I w i) (stateAt I w j) = true

@[simp] theorem periodicStream_eq (c : Word) (t : Nat) :
    periodicStream c t = (c[t % c.length]?).getD false := rfl

theorem prefixStream_eq_prefix {w c : Word} {t : Nat} (ht : t < w.length) :
    prefixStream w c t = (w[t]?).getD false := by
  simp [prefixStream, ht]

theorem prefixStream_eq_tail {w c : Word} {t : Nat} (ht : w.length ≤ t) :
    prefixStream w c t = periodicStream c (t - w.length) := by
  simp [prefixStream, Nat.not_lt.mpr ht]

theorem prefixStream_eq_wordOf {w c : Word} {t : Nat} (ht : t < w.length) :
    prefixStream w c t = w[t]'(by omega) := by
  simpa [prefixStream, ht] using (List.getElem?_eq_getElem ht)

theorem witness_safeRun (I : Instance k) {w : Word} {q : Fin k}
    (hw : Witness I w) (hq : stateAt I w w.length = some q) :
    SafeRun I I.initial w q := by
  refine ⟨?_, witness_safeCut I hw⟩
  simpa [stateAt] using hq

end PeriodicRun
end Subtail

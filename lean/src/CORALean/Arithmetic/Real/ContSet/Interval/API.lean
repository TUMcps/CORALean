import CORALean.Arithmetic.Real.ContSet.ContSet.API

/-!
# Intervals: representation and operations

CORA's `interval`, with the same `inf` and `sup` fields.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n m : ℕ}

structure Interval (n : ℕ) where
  inf : Vec ℝ n
  sup : Vec ℝ n

/-- `sup i < inf i` denotes the empty set `∅` -/
def Interval.construct (I : Interval n) : Set (Vec ℝ n) :=
  {x | ∀ i, I.inf i ≤ x i ∧ x i ≤ I.sup i}

/-- checked in `Theorems.isNonempty_iff` -/
def Interval.IsNonempty (I : Interval n) : Prop := ∀ i, I.inf i ≤ I.sup i

def Interval.plus (I₁ I₂ : Interval n) : Interval n where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

def Interval.mtimes (M : Mat ℝ m n) (I : Interval n) : Interval m where
  inf := fun i => ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
  sup := fun i => ∑ k, max (M i k * I.inf k) (M i k * I.sup k)

end CORALean.Arithmetic.Real

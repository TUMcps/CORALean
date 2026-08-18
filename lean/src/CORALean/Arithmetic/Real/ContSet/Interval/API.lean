import CORALean.Arithmetic.Real.ContSet.Interval.Structure

/-!
# Intervals: the operations

CORA's `interval` operations over the structure in `Structure`.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n m : ℕ}

def Interval.plus (I₁ I₂ : Interval n) : Interval n where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

def Interval.mtimes (M : Mat ℝ m n) (I : Interval n) : Interval m where
  inf := fun i => ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
  sup := fun i => ∑ k, max (M i k * I.inf k) (M i k * I.sup k)

end CORALean.Arithmetic.Real

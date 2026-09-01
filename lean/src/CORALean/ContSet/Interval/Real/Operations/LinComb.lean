import CORALean.ContSet.Interval.Real.Interval

/-!
# Intervals: the linear combination of two

The box around both, which is what a segment between two boxes needs: an
interval cannot hold the exact hull of two of them — that is a polytope in
general — so this over-approximates, as CORA's does.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Interval.linComb (I₁ I₂ : Interval n) : Interval n where
  inf := fun i => min (I₁.inf i) (I₂.inf i)
  sup := fun i => max (I₁.sup i) (I₂.sup i)

end CORALean.Real

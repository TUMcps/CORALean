import CORALean.ContSet.Capsule.Real.Operations.ConvHull
import CORALean.ContSet.Capsule.Real.Cost.Radius

/-!
# `Capsule.convHullCost`

Asserted, not proved: `Operations/ConvHull.lean` forms `c_ = (c + S.c) / 2`
(`2 * n`), `g_ = c - c_` (`n`), two `Capsule.radius` and their `max` (one).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.convHull` costs at `Vec ℝ n`. -/
def Capsule.convHullCost (n : ℕ) : Cost := ⟨3 * n⟩ + (2 : ℕ) • Capsule.radiusCost n + ⟨1⟩

/-- Monotone in the dimension. -/
theorem Capsule.convHullCost_mono {n n' : ℕ} (h : n ≤ n') :
    Capsule.convHullCost n ≤ Capsule.convHullCost n' := by
  simp only [Capsule.convHullCost, Capsule.radiusCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.HPolytope.Real.Definitions.PolyNorm
import Mathlib.Algebra.Order.Group.Finset

/-!
# `polyNorm` against a bound

`S_P(x) ≤ t` iff `0 ≤ t` and every row's ratio is at most `t`: a fold of `max` is below `t`
exactly when its start and every term are.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {s n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.polyNorm_le_iff {H : Mat ℝ s n} {h : Vec ℝ s} {x : Vec ℝ n} {t : ℝ} :
    HPolytope.polyNorm H h x ≤ t ↔ 0 ≤ t ∧ ∀ i, (H *ᵥ x) i / h i ≤ t := by
  simp [HPolytope.polyNorm, Finset.fold_max_le]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

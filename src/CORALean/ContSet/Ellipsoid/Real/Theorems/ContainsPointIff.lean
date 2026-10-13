import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsPoint
import CORALean.ContSet.Ellipsoid.Real.Theorems.EllipsoidNormLeOneIff

/-!
# `Ellipsoid.containsPoint` is membership

For a full-rank ellipsoid, CORA's point test `ellipsoidNorm(p - c) <= 1` holds exactly when `p`
lies in the ellipsoid: exact, at tolerance `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.containsPoint_iff (E : Ellipsoid n) (hr : E.rank = n) (p : Vec ℝ n) :
    E.containsPoint p ↔ p ∈ E.construct := by
  have := E.ellipsoidNorm_le_one_iff hr (p - E.q)
  rw [add_sub_cancel] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

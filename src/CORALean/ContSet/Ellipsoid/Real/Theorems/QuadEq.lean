import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import CORALean.ContSet.Ellipsoid.Real.Theorems.DotTranspose

/-!
# The quadratic form of an ellipsoid's shape is a squared norm

`vᵀ Q v = (Gᵀ v)ᵀ (Gᵀ v)` for `Q = G Gᵀ`, so it is `‖Gᵀ v‖₂²` and nonnegative.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.quad_eq (E : Ellipsoid n) (v : Vec ℝ n) :
    v ⬝ᵥ (E.shape *ᵥ v) = (E.Gᵀ *ᵥ v) ⬝ᵥ (E.Gᵀ *ᵥ v) := by
  rw [Ellipsoid.shape, ← Matrix.mulVec_mulVec, Ellipsoid.dot_transpose]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

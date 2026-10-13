import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# The transpose moves across the dot product

`(Gᵀ w) · a = w · (G a)`, the identity behind the support point and the shape matrix `G Gᵀ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.dot_transpose {k : ℕ} (G : Mat ℝ n k) (w : Vec ℝ n) (a : Vec ℝ k) :
    (Gᵀ *ᵥ w) ⬝ᵥ a = w ⬝ᵥ (G *ᵥ a) := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

/-!
# The bilinear form family in coordinates

`quadBilin D x y i = ∑ j, ∑ k, D i j k * (x j * y k)`, which is the shape the paper writes its
second-order terms in. Its own file, read by the exact and the float `varInputs` theorems.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n o : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.quadBilin_apply (D : Fin n → Mat ℝ o o) (x y : Vec ℝ o) (i : Fin n) :
    PolyZonotope.quadBilin D x y i = ∑ j, ∑ k, D i j k * (x j * y k) := by
  simp only [PolyZonotope.quadBilin, LinearMap.mk₂_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Algebra.BigOperators.Pi

/-!
# Coordinates of a point of a planar zonotope

`(c + ∑ βⱼ gⱼ)_k = c_k + ∑ βⱼ g_{j,k}`.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.comb_apply (Z : Zonotope (Vec ℝ 2)) (β : Fin Z.h → ℝ) (k : Fin 2) :
    (Z.c + ∑ j, β j • Z.G j) k = Z.c k + ∑ j, β j * Z.G j k := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

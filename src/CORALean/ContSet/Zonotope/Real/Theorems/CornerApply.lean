import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope
import CORALean.Global.Tensor

/-!
# Coordinates of a sign corner

The coordinates of `corner s` in a planar zonotope: `c_k + ∑ ±g_{j,k}`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.corner_apply (Z : Zonotope (Vec ℝ 2)) (s : Fin Z.h → Bool) (k : Fin 2) :
    Z.corner s k = Z.c k + ∑ j, (if s j then (1 : ℝ) else -1) * Z.G j k := by
  simp only [Zonotope.corner, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

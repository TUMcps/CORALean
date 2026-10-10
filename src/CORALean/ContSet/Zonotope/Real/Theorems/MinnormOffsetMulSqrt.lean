import CORALean.ContSet.Zonotope.Real.Operations.MinnormOffset
import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalDotSelfPos

/-!
# The unit-row offset times the row length is the offset

`minnormOffset` divides `Δd = Σᵤ |C G⁽ᵘ⁾|` by `‖C‖₂`; multiplying back returns `Δd`, which is the
bound the facet inequality of `hRep_eq` states.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnormOffset_mul_sqrt (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h)
    (hC : Z.facetNormal S ≠ 0) :
    Z.minnormOffset S * Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S) =
      ∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ| := by
  have hs := Real.sqrt_pos.mpr (Zonotope.facetNormal_dotProduct_self_pos Z S hC)
  unfold Zonotope.minnormOffset
  field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

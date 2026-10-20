module

public import CORALean.ContSet.Zonotope.Real.Operations.MinnormOffset
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalDotSelfPos

@[expose] public section

/-!
# The unit-row offset times the row length is the offset

`minnormOffset` divides `Δd = Σᵤ |C G⁽ᵘ⁾|` by `‖C‖₂`; multiplying back returns `Δd`, which is the
bound the facet inequality of `hRep_eq` states.

## Inputs
* `Z` – zonotope
* `S` – selected generator indices

## Hypotheses
* `hC` – facet normal nonzero

## Conclusion
* the offset times the normal length equals the generator reach
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

module

public import CORALean.ContSet.Zonotope.Real.Operations.FacetNormal
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# A nonzero facet normal has positive square length

The step every unit-row argument starts with: dividing by `‖C‖₂ = sqrt (C ⬝ C)` needs `C ⬝ C > 0`.

## Inputs
* `Z` – zonotope
* `S` – selected generator indices

## Hypotheses
* `hC` – facet normal nonzero

## Conclusion
* the facet normal has positive squared norm
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

theorem Zonotope.facetNormal_dotProduct_self_pos (Z : Zonotope (Vec ℝ (n + 1)))
    (S : Fin n → Fin Z.h) (hC : Z.facetNormal S ≠ 0) :
    0 < Z.facetNormal S ⬝ᵥ Z.facetNormal S :=
  lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    (Ne.symm (mt dotProduct_self_eq_zero.mp hC))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

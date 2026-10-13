import CORALean.ContSet.Zonotope.Real.Operations.MinnormOffset

/-!
# `Zonotope.minnormPoint`

CORA's second output of `minnorm`, `x = A(ind,:)' * b(ind) + Z.c`: the foot of the perpendicular
from the centre on the facet hyperplane of the row `ind` that attains the minimum, `Ĉ · b + c`
at the unit row `Ĉ = C / ‖C‖₂` and offset `b`.

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ĉ_S · b_S + c`: the point of the facet hyperplane of `S` nearest the centre. -/
noncomputable def Zonotope.minnormPoint (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h) :
    Vec ℝ (n + 1) :=
  let Chat := (Real.sqrt (Z.facetNormal S ⬝ᵥ Z.facetNormal S))⁻¹ • Z.facetNormal S  -- unit row
  Z.c + Z.minnormOffset S • Chat

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

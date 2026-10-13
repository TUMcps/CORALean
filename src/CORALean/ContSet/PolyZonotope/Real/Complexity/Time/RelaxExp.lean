import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxWidth

/-!
# `PolyZonotope.relaxExpCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExp.lean` adds the two
named generators (`n`) and scales the first by `ξ_E` (`relaxWidth`, then `n`
products). The kept generators and exponent columns are copied. The factor
count and the generator count do not enter.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExp` costs at `Vec ℝ n`. -/
def PolyZonotope.relaxExpCost (n : ℕ) : Cost := ⟨2 * n⟩ + PolyZonotope.relaxWidthCost

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Operations.Capsule_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleConstructEqSegmentAddBall
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidConPolyZonoExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConPolyZonoExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact

@[expose] public section

/-!
# CORA's `conPolyZono(C)` is the capsule

The capsule is its segment plus its ball (`Capsule.construct_eq_segment_add_ball`, for `0 ≤ r`),
each conversion is exact, and so is the sum (`ConPolyZono.plus_exact`), taken here in the order
CORA takes it (segment, ball).

## Inputs
* `C` – capsule

## Hypotheses
* `hr` – radius nonnegative

## Conclusion
* capsule equals its constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `conPolyZono(C)` denotes the capsule, for a nonnegative radius. -/
theorem Capsule.conPolyZono_exact (C : Capsule n) (hr : 0 ≤ C.r) :
    C.construct = C.conPolyZono.construct := by
  rw [C.construct_eq_segment_add_ball hr, Capsule.conPolyZono, ← ConPolyZono.plus_exact,
    ← Ellipsoid.conPolyZono_exact, ← Zonotope.conPolyZono_exact]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

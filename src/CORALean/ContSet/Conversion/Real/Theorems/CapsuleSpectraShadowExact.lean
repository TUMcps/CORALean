module

public import CORALean.ContSet.Conversion.Real.Operations.Capsule_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Theorems.CapsuleConstructEqSegmentAddBall
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSpectraShadowExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeSpectraShadowExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact

@[expose] public section

/-!
# CORA's `spectraShadow(C)` is the capsule

The capsule is its segment plus its ball (`Capsule.construct_eq_segment_add_ball`, for `0 ≤ r`),
each conversion is exact, and so is the sum (`SpectraShadow.plus_exact`), taken here in the order
CORA takes it (ball, segment).

## Inputs
* `C` – capsule

## Hypotheses
* `hr` – radius nonnegative

## Conclusion
* capsule equals its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `spectraShadow(C)` denotes the capsule, for a nonnegative radius. -/
theorem Capsule.spectraShadow_exact (C : Capsule n) (hr : 0 ≤ C.r) :
    C.construct = C.spectraShadow.construct := by
  rw [C.construct_eq_segment_add_ball hr, Capsule.spectraShadow, ← SpectraShadow.plus_exact,
    ← Ellipsoid.spectraShadow_exact, ← Zonotope.spectraShadow_exact]
  exact add_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

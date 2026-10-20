module

public import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Theorems.CapsuleConstructSubsetSegmentAddBall
public import CORALean.ContSet.Conversion.Float.Theorems.EllipsoidSpectraShadowExact
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeSpectraShadowContains
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter

@[expose] public section

/-!
# A capsule lies in its spectrahedral shadow, over a floating-point scalar

The capsule lies in its segment plus its ball (`Capsule.construct_subset_segment_add_ball`); the
ball's shadow is exact, its rounded-up shape being positive semi-definite
(`Ellipsoid.ball_posSemidef`), the segment's encloses it, and the sum encloses theirs.

## Inputs
* `C` – capsule

## Hypotheses
* none

## Conclusion
* capsule is contained in its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float capsule lies in its shadow. -/
theorem Capsule.spectraShadow_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.spectraShadow.construct := by -- --- PROOF ---
  refine subset_trans C.construct_subset_segment_add_ball ?_
  rw [add_comm]
  exact subset_trans (Set.add_subset_add
    (Ellipsoid.spectraShadow_exact _ (Ellipsoid.ball_posSemidef C.r)).subset
    (Zonotope.spectraShadow_contains _)) (SpectraShadow.plus_outer _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

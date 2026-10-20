module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A box as a zonotope, over a floating-point scalar: `reaches`

## Inputs
* `I` – interval
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* center plus or minus the radius reaches both ends
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.reaches (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    toReal (I.center i) - toReal (I.radiusFrom i) ≤ toReal (I.inf i)
      ∧ toReal (I.sup i) ≤ toReal (I.center i) + toReal (I.radiusFrom i) := by -- --- PROOF ---
  have hhi := sub_le_subUp (I.sup i) (I.center i)
  have hlo := sub_le_subUp (I.center i) (I.inf i)
  rw [Interval.radiusFrom, toReal_maximum]
  constructor
  · have h : toReal (I.center i) - toReal (I.inf i) ≤ max
        (toReal (subUp (I.sup i) (I.center i))) (toReal (subUp (I.center i) (I.inf i))) :=
      le_trans hlo (le_max_right _ _)
    linarith
  · have h : toReal (I.sup i) - toReal (I.center i) ≤ max
        (toReal (subUp (I.sup i) (I.center i))) (toReal (subUp (I.center i) (I.inf i))) :=
      le_trans hhi (le_max_left _ _)
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

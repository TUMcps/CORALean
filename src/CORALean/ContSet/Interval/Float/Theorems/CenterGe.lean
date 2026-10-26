module

public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.center` is at least the real midpoint

The sum rounds up and `half` is exact, so the stored `center` is at least the midpoint of the
stored bounds read as reals.

## Inputs
* `I` – interval box
* `i` – coordinate index

## Hypotheses
* none

## Conclusion
* the rounded center is at least the real midpoint
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Interval.aux_center_nominal (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    I.nominal.center i = (toReal (I.inf i) + toReal (I.sup i)) / 2 := by
  show (2:ℝ)⁻¹ * (toReal (I.inf i) + toReal (I.sup i)) = _
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.center_ge (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    I.nominal.center i ≤ toReal (I.center i) := by
  rw [Interval.aux_center_nominal, Interval.center, toReal_half]
  have := add_le_addUp (I.inf i) (I.sup i)
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

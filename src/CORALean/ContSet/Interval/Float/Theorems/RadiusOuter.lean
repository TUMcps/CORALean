module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.radius` bounds the real half-width

`half` is exact and the difference rounds up, so the stored radius is at least the real one, and
the real one is `Real.Interval.radius`, the quantity every enclosure proof off a box reads.

## Inputs
* `I` – interval box
* `i` – coordinate index

## Hypotheses
* none

## Conclusion
* the float radius is at least the real half-width of coordinate `i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.radius_ge (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    I.nominal.radius i ≤ toReal (I.radius i) := by -- --- PROOF ---
  have h : I.nominal.radius i = (toReal (I.sup i) - toReal (I.inf i)) / 2 := by
    show (2:ℝ)⁻¹ * (toReal (I.sup i) - toReal (I.inf i)) = _
    ring
  rw [h, Interval.radius, toReal_half]
  have := sub_le_subUp (I.sup i) (I.inf i)
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

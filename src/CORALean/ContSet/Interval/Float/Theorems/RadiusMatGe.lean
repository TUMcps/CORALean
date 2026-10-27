module

public import CORALean.ContSet.Interval.Float.Operations.RadiusMat
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.radiusMat` bounds the real half-width

`half` is exact and the difference rounds up, so each stored half-width is at least the real one,
the quantity every enclosure proof off an interval matrix reads.

## Inputs
* `I` – interval matrix
* `i` – row index
* `j` – column index

## Hypotheses
* none

## Conclusion
* the stored half-width of entry `(i, j)` is at least the real one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.radiusMat_ge (I : Interval (Mat 𝕋 m n)) (i : Fin m) (j : Fin n) : -- --- CONCL ---
    I.nominal.radius i j ≤ toReal (I.radiusMat i j) := by -- --- PROOF ---
  have h : I.nominal.radius i j = (toReal (I.sup i j) - toReal (I.inf i j)) / 2 := by
    show (2:ℝ)⁻¹ * (toReal (I.sup i j) - toReal (I.inf i j)) = _
    ring
  rw [h, Interval.radiusMat, toReal_half]
  have := sub_le_subUp (I.sup i j) (I.inf i j)
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

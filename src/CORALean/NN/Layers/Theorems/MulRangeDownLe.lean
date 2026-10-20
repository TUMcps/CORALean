module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.MulRangeDown

@[expose] public section

/-!
# The lower product bound

Multiplication by `a` is monotone one way or the other, so one end of the bracket bounds it.

## Inputs
* `a` – factor
* `lo` – lower end of the bracket
* `hi` – upper end of the bracket
* `x` – real number in the bracket

## Hypotheses
* `h1` – number is above the lower end
* `h2` – number is below the upper end

## Conclusion
* the lower product bound is at most the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mulRangeDown_le {a lo hi : 𝕋} {x : ℝ} (h1 : toReal lo ≤ x) (h2 : x ≤ toReal hi) :
    toReal (mulRangeDown a lo hi) ≤ toReal a * x := by -- --- PROOF ---
  rw [mulRangeDown, toReal_minimum]
  -- multiplication by `a` is monotone one way or the other, so one end bounds it
  rcases le_or_gt 0 (toReal a) with ha | ha
  · exact le_trans (min_le_left _ _)
      (le_trans (mulDown_le_mul a lo) (mul_le_mul_of_nonneg_left h1 ha))
  · exact le_trans (min_le_right _ _)
      (le_trans (mulDown_le_mul a hi) (mul_le_mul_of_nonpos_left h2 ha.le))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

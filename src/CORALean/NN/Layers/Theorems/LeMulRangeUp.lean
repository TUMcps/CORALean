module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.Basic

@[expose] public section

/-!
# The upper product bound

The same case split on `a`'s sign, each end now reached from above.

## Inputs
* `a` – factor
* `lo` – lower end of the bracket
* `hi` – upper end of the bracket
* `x` – real number in the bracket

## Hypotheses
* `h1` – number is above the lower end
* `h2` – number is below the upper end

## Conclusion
* the product is at most the upper product bound
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

theorem le_mulRangeUp {a lo hi : 𝕋} {x : ℝ} (h1 : toReal lo ≤ x) (h2 : x ≤ toReal hi) :
    toReal a * x ≤ toReal (mulRangeUp a lo hi) := by -- --- PROOF ---
  rw [mulRangeUp, toReal_maximum]
  -- the same case split, each end now reached from above
  rcases le_or_gt 0 (toReal a) with ha | ha
  · exact le_trans (le_trans (mul_le_mul_of_nonneg_left h2 ha) (mul_le_mulUp a hi))
      (le_max_right _ _)
  · exact le_trans (le_trans (mul_le_mul_of_nonpos_left h1 ha.le) (mul_le_mulUp a lo))
      (le_max_left _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

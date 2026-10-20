module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An interval as a right-hand side and its slack

A value in `[lo, hi]` is within the stored width `hi - lo`, rounded up, of `lo`: how an interval a
float operation encloses a row by is recorded as the row's `b` and `b_error`.

## Inputs
* `lo` – lower endpoint
* `hi` – upper endpoint
* `v` – real value

## Hypotheses
* `h₁` – value is at least the lower endpoint
* `h₂` – value is at most the upper endpoint

## Conclusion
* distance to the lower endpoint is within the rounded-up width
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A value in `[lo, hi]` is within the stored width `hi - lo`, rounded up, of `lo`: an interval
recorded as a right-hand side `lo` and its slack. -/
theorem ConPolyZono.abs_sub_le_subUp {lo hi : 𝕋} {v : ℝ} (h₁ : toReal lo ≤ v)
    (h₂ : v ≤ toReal hi) : |v - toReal lo| ≤ |toReal (subUp hi lo)| := by
  rw [abs_of_nonneg (sub_nonneg.mpr h₁)]
  exact (by linarith [sub_le_subUp hi lo] : v - toReal lo ≤ _).trans (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

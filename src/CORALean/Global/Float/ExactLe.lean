module

public import CORALean.Global.Float.Interfaces
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# Every format with `ToRat` compares exactly

`ExactLe` from the exact decoding into ℚ: two scalars compare as their rationals do, and are within
a tolerance as they are, and the rationals read as the reals `toReal` gives. A NaN compares as the
number it decodes to, like any other scalar; `noNaN` is what keeps one out of a reported result.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ======================================  MAIN INSTANCE  ======================================= --

/-- Two scalars compare as the rationals they decode to, and are within a tolerance as they are. -/
instance : ExactLe 𝕋 where
  le a b := decide (ToRat.toRat a ≤ ToRat.toRat b)
  le_iff a b := by
    rw [decide_eq_true_iff, ← ToRat.toReal_toRat a, ← ToRat.toReal_toRat b, Rat.cast_le]
  withinTol tol a b := decide (|ToRat.toRat a - ToRat.toRat b| ≤ ToRat.toRat tol ∨
    |ToRat.toRat a - ToRat.toRat b| ≤ ToRat.toRat tol * min |ToRat.toRat a| |ToRat.toRat b|)
  withinTol_iff tol a b := by
    rw [decide_eq_true_iff, ← ToRat.toReal_toRat a, ← ToRat.toReal_toRat b,
      ← ToRat.toReal_toRat tol]
    norm_cast

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

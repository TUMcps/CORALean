module

public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# Every point of a capsule's error box is within `errorNorm` of the origin

Each coordinate of a point of the box lies between the two ends, so its absolute value is at most
the larger end magnitude, `Interval.normMag`; the Euclidean norm of the point is then at most the
norm of `normMag`, which `normUp` rounds up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the error box is within `errorNorm`: per coordinate, the larger end magnitude. -/
theorem Capsule.norm₂_le_errorNorm (k : ℕ) (C : Capsule 𝕋 n) {e : Vec ℝ n}
    (he : e ∈ C.I_error.construct) : ‖e‖₂ ≤ toReal (C.errorNorm k) :=
  norm₂_le_normUp k fun j => by
    rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute,
      abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    exact abs_le_max_abs_abs (he j).1 (he j).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

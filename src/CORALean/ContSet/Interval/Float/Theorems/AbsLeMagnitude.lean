module

public import CORALean.ContSet.Interval.Float.Operations.Magnitude

@[expose] public section

/-!
# A point of an interval vector is within its magnitude of the origin

## Inputs
* `I` – interval box
* `b` – point of the box
* `i` – coordinate index

## Hypotheses
* `hb` – `b` lies in `I`

## Conclusion
* entry `i` of `b` is bounded in absolute value by the magnitude of `I`
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.abs_le_magnitude {I : Interval (Vec 𝕋 n)} {b : Vec ℝ n} (hb : b ∈ I.construct)
    (i : Fin n) : |b i| ≤ toReal (I.magnitude i) := by
  have h : toReal (I.inf i) ≤ b i ∧ b i ≤ toReal (I.sup i) := hb i
  rw [Interval.magnitude, toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h.1 h.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Float.Operations.Norm
public import CORALean.ContSet.Interval.Real.Theorems.NormLe

@[expose] public section

/-!
# `Interval.norm` bounded without a square root

`normSq` rounds the squared length of the larger endpoint magnitudes up, and a caller-supplied
`σ` with `normSq ≤ σ·σ` (the second rounded down) certifies `|σ|` as an upper bound of the exact
layer's `Interval.norm`.

## Inputs
* `I` – interval box
* `σ` – certified bound of the norm

## Hypotheses
* `hσ` – squared norm at most `σ` squared

## Conclusion
* the nominal norm is at most the certified bound
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

private theorem Interval.aux_normMag_ge (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    max |toReal (I.inf i)| |toReal (I.sup i)| ≤ toReal (I.normMag i) := by
  rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.norm_nominal_le (I : Interval (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal I.normSq ≤ toReal (mulDown σ σ)) :
    I.nominal.norm ≤ toReal (absolute σ) := by
  refine norm₂_le_of_sq_le (m := I.normMag) (fun i => ?_) hσ
  -- the endpoint magnitude is nonnegative, so it is its own absolute value
  rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
  exact I.aux_normMag_ge i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

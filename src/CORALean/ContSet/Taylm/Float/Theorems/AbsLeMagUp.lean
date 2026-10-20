module

public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.magUp` bounds the hull

Every point of the hull of the center and the range has absolute value at most
`Taylm.magUp`, and so has the center itself.

## Inputs
* `T` – Taylor model
* `ξ` – point

## Hypotheses
* `hξ` – point lies in the model's hull

## Conclusion
* the magnitude bound dominates the point
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.abs_le_magUp (T : Taylm 𝕋 n) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (min (toReal T.constCoef) (toReal T.bounds.inf))
      (max (toReal T.constCoef) (toReal T.bounds.sup))) : -- --- CONCL ---
    |ξ| ≤ toReal T.magUp := by -- --- PROOF ---
  have hm : toReal T.magUp = max |toReal T.constCoef|
      (max |toReal T.bounds.inf| |toReal T.bounds.sup|) := by
    rw [Taylm.magUp, toReal_maximum, toReal_maximum, toReal_absolute, toReal_absolute,
      toReal_absolute]
  have h1 := le_max_left |toReal T.constCoef| (max |toReal T.bounds.inf| |toReal T.bounds.sup|)
  have h2 := le_max_left |toReal T.bounds.inf| |toReal T.bounds.sup|
  have h3 := le_max_right |toReal T.bounds.inf| |toReal T.bounds.sup|
  have h4 := le_max_right |toReal T.constCoef| (max |toReal T.bounds.inf| |toReal T.bounds.sup|)
  rw [hm]
  rw [abs_le]
  constructor
  · rcases min_le_iff.1 hξ.1 with h5 | h5
    · linarith [neg_abs_le (toReal T.constCoef)]
    · linarith [neg_abs_le (toReal T.bounds.inf)]
  · rcases le_max_iff.1 hξ.2 with h5 | h5
    · linarith [le_abs_self (toReal T.constCoef)]
    · linarith [le_abs_self (toReal T.bounds.sup)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

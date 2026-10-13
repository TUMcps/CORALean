module

public import CORALean.ContSet.Interval.Float.Operations.NonemptyHull
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty

@[expose] public section

/-!
# The nonempty hull is nonempty

The raised upper bound is a maximum with the lower one, which `toReal_maximum` reads exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.nonemptyHull_isNonempty (I : Interval (Vec 𝕋 n)) :
    I.nonemptyHull.nominal.IsNonempty := fun i => by
  show toReal (I.inf i) ≤ toReal (maximum (I.inf i) (I.sup i))
  rw [toReal_maximum]
  exact le_max_left _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

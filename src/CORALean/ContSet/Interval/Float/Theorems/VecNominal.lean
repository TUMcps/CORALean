module

public import CORALean.ContSet.Interval.Float.Operations.Vec
public import CORALean.ContSet.Interval.Real.Operations.Vec

@[expose] public section

/-!
# `Interval.vec` stacks the nominal interval matrix

The stacking moves entries without rounding, so the nominal interval of the stacked bounds is the
exact layer's stacking of the nominal interval matrix.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the nominal interval of `vec` is `vec` of the nominal interval matrix
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

theorem Interval.vec_nominal (I : Interval (Mat 𝕋 m n)) :
    I.vec.nominal = I.nominal.vec := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

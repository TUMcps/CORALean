module

public import CORALean.ContSet.Interval.Float.Theorems.VecNominal
public import CORALean.ContSet.Interval.Real.Theorems.VecConstruct
public import CORALean.Global.MatVec

@[expose] public section

/-!
# `Interval.vec` is exactly the stacked set

Stacking commutes with reading the floats as reals, so the stacked box denotes the exact layer's
stacking of the nominal box, which is the image of the matrices of the box under the column-major
vectorisation.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the stacked box denotes exactly the stackings of the members
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

theorem Interval.vec_exact (I : Interval (Mat 𝕋 m n)) :
    I.vec.construct = matVecEquiv '' I.construct :=
  Real.Interval.vec_construct I.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

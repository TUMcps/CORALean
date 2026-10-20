module

public import CORALean.ContSet.Interval.Float.Operations.Transpose
public import CORALean.ContSet.Interval.Real.Theorems.TransposeExact

@[expose] public section

/-!
# `Interval.transpose` is exactly the transposed set

Transposition commutes with reading the floats as reals, so the stored box denotes the exact layer's
transpose of the reading, and `Real.Interval.transpose_exact` carries over.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the transposed box is exactly the set of transposes
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.transpose_exact (I : Interval (Mat 𝕋 m n)) :
    I.transpose.construct = Matrix.transpose '' I.construct :=
  Real.Interval.transpose_exact I.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

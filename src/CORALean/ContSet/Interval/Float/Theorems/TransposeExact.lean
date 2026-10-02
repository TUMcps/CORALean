import CORALean.ContSet.Interval.Float.Operations.Transpose
import CORALean.ContSet.Interval.Real.Theorems.TransposeExact

/-!
# `Interval.transpose` is exactly the transposed set

Transposition commutes with reading the floats as reals, so the stored box denotes the exact layer's
transpose of the reading, and `Real.Interval.transpose_exact` carries over.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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

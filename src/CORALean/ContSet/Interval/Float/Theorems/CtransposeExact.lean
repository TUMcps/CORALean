import CORALean.ContSet.Interval.Float.Operations.Ctranspose
import CORALean.ContSet.Interval.Real.Theorems.CtransposeExact

/-!
# `Interval.ctranspose` is exactly the conjugate-transposed set

The same for the conjugate transpose, which over the reals a float reads as is the transpose.
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

theorem Interval.ctranspose_exact (I : Interval (Mat 𝕋 m n)) :
    I.ctranspose.construct = Matrix.conjTranspose '' I.construct :=
  Real.Interval.ctranspose_exact I.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

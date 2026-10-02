import CORALean.ContSet.Interval.Float.Operations.DiagVec
import CORALean.ContSet.Interval.Real.Theorems.DiagVecExact

/-!
# `Interval.diagVec` over floats is exact

Reading the diagonal commutes with reading the floats as reals, so the stored box denotes the
exact layer's diagonal box of the reading.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.diagVec_exact (I : Interval (Mat 𝕋 n n))
    (hI : ∀ i j, toReal (I.inf i j) ≤ toReal (I.sup i j)) :
    I.diagVec.construct = (fun A i => A i i) '' I.construct :=
  Real.Interval.diagVec_exact I.nominal hI

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

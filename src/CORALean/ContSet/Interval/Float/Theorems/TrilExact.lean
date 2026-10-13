import CORALean.ContSet.Interval.Float.Operations.Tril
import CORALean.ContSet.Interval.Float.Theorems.MaskExact

/-!
# `Interval.tril` over floats is exact

`Interval.mask_exact` at the `tril` pattern: the stored box denotes the image of the reading under
`tril`, for a box with no empty entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.tril_exact (K : ℕ) (I : Interval (Mat 𝕋 m n))
    (hI : ∀ i j, toReal (I.inf i j) ≤ toReal (I.sup i j)) :
    (I.tril K).construct = (fun (A : Mat ℝ m n) (i : Fin m) (j : Fin n) =>
      if (j : ℕ) ≤ (i : ℕ) + K then A i j else 0) '' I.construct :=
  Interval.mask_exact _ I hI

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

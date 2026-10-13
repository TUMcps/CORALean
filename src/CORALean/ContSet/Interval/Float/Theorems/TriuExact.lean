module

public import CORALean.ContSet.Interval.Float.Operations.Triu
public import CORALean.ContSet.Interval.Float.Theorems.MaskExact

@[expose] public section

/-!
# `Interval.triu` over floats is exact

`Interval.mask_exact` at the `triu` pattern: the stored box denotes the image of the reading under
`triu`, for a box with no empty entry.
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

theorem Interval.triu_exact (K : ℕ) (I : Interval (Mat 𝕋 m n))
    (hI : ∀ i j, toReal (I.inf i j) ≤ toReal (I.sup i j)) :
    (I.triu K).construct = (fun (A : Mat ℝ m n) (i : Fin m) (j : Fin n) =>
      if (i : ℕ) + K ≤ (j : ℕ) then A i j else 0) '' I.construct :=
  Interval.mask_exact _ I hI

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

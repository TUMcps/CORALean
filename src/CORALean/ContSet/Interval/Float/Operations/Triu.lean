import CORALean.ContSet.Interval.Float.Operations.Mask

/-!
# `Interval.triu` over floats

`Interval.mask` at the entries on or above the `K`-th superdiagonal.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.triu (K : ℕ) (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  I.mask (fun i j => (i : ℕ) + K ≤ (j : ℕ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

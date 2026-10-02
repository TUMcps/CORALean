import CORALean.ContSet.Interval.Float.Operations.Mask

/-!
# `Interval.tril` over floats

`Interval.mask` at the entries on or below the `K`-th superdiagonal.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.tril (K : ℕ) (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  I.mask (fun i j => (j : ℕ) ≤ (i : ℕ) + K)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.Global.Float.FloatOps

/-!
# `halfMat`

`½ I`, the scaling of `varInputsFloat`'s second-order part. Halving is exact in a binary format,
so `mtimes` by it costs the error box nothing it does not already carry.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `½ I`, the scaling of the second-order part. -/
def halfMat (n : ℕ) : Mat 𝕋 n n := fun i j => if i = j then half one else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

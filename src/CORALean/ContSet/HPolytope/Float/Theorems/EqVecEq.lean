import CORALean.ContSet.HPolytope.Float.Operations.EqVec
import CORALean.ContSet.HPolytope.Float.Theorems.EqScalarEq

/-!
# Rows certified equal read equal

Entry by entry, so the dot product with any point agrees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.toReal_eq_of_eqVec {u v : Vec 𝕋 n} (h : HPolytope.eqVec u v = true) (j : Fin n) :
    toReal (u j) = toReal (v j) :=
  HPolytope.toReal_eq_of_eqScalar (List.all_eq_true.mp h j (List.mem_finRange j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

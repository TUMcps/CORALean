import CORALean.ContSet.HPolytope.Float.Operations.EqScalar
import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# A certified equal pair reads equal

`eqScalar a b = true` gives `toReal a = toReal b`, each `le` being sound.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.toReal_eq_of_eqScalar {a b : 𝕋} (h : HPolytope.eqScalar a b = true) :
    toReal a = toReal b := by
  simp only [HPolytope.eqScalar, Bool.and_eq_true] at h
  exact le_antisymm (toReal_le_of_le h.1) (toReal_le_of_le h.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

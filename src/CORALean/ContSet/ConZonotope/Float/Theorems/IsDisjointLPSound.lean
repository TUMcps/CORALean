import CORALean.ContSet.ConZonotope.Float.Operations.IsDisjointLP
import CORALean.ContSet.ConZonotope.Float.Theorems.SeparatesAlongSound

/-!
# `ConZonotope.isDisjointLP` is sound when `true`

A direction along which the first set's upper bound lies strictly below the
second's lower bound leaves no point for both, whichever direction it is. So
the verdict is sound for every direction the simplex could have proposed; only
its completeness depends on the simplex, and none is claimed.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isDisjointLP_sound {cZ₁ cZ₂ : ConZonotope 𝕋 n}
    (h : cZ₁.isDisjointLP cZ₂ = true) : Disjoint cZ₁.construct cZ₂.construct := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact ConZonotope.separatesAlong_sound h
  · exact ConZonotope.separatesAlong_sound h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

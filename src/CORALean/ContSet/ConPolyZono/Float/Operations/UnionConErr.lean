import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConInt
import CORALean.Global.Float.IntRound

/-!
# `ConPolyZono.unionConErr`

What storing the selector row's integers from below costs: the gap between each
integer's two directed roundings, summed upward. A factor in `[-1,1]` makes a
monomial at most `1` in absolute value, so this bounds how far the stored row can
stray from the scaled one.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The summed gap between the two roundings of every coefficient. -/
def ConPolyZono.unionConErr (p₁ p₂ : ℕ) : 𝕋 :=
  sumUp fun l => subUp (intUp (ConPolyZono.unionConInt p₁ p₂ l))
    (intDown (ConPolyZono.unionConInt p₁ p₂ l))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

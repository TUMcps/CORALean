import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.keepColumn`

Whether a generator column is kept by `compact_(Z, 'zeros')` at tolerance `0`: it is dropped
exactly when every entry is certified zero by `le` in both directions. The certified test is a
proof when it holds, so a dropped column is zero as reals; a zero column it cannot certify is kept.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether column `j` is not certified zero. -/
def Zonotope.keepColumn (Z : Zonotope 𝕋 n) (j : Fin Z.h) : Bool :=
  !(List.finRange n).all fun i => le (Z.G j i) zero && le zero (Z.G j i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.Interval.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Interval.Float.Operations.RepresentsaEmptySet

/-!
# `PolyZonotope.representsa_emptySet`, over a floating-point scalar

CORA's `@polyZonotope/representsa_` at type `emptySet`: a polynomial zonotope's nominal part is
never empty, so only an empty error box (some coordinate with `sup < inf`, by `ltStrict`) makes
the set empty; a `true` is sound.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.representsa_emptySet (pZ : PolyZonotope 𝕋 n) : Bool :=
  pZ.err.representsa_emptySet

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

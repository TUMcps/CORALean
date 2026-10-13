module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.Interval.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Float.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `PolyZonotope.representsa_emptySet`, over a floating-point scalar

CORA's `@polyZonotope/representsa_` at type `emptySet`: a polynomial zonotope's nominal part is
never empty, so only an empty error box (some coordinate with `sup < inf`, by `ltStrict`) makes
the set empty; a `true` is sound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.representsa_emptySet (pZ : PolyZonotope (Vec 𝕋 n)) : Bool :=
  pZ.err.representsa_emptySet

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

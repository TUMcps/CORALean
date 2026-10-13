module

public import CORALean.ContSet.ConZonotope.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_ConZonotope

@[expose] public section

/-!
# `ZonoBundle.representsa_emptySet`, over a floating-point scalar

CORA decides emptiness of the intersection with one linear program over the stacked coefficients.
`ZonoBundle.conZonotopeAll` is that program's feasible set, enclosed, and
`ConZonotope.representsa_emptySet` certifies it empty by a Farkas certificate the exact simplex
proposes and rounded arithmetic checks. One-sided: `true` proves the intersection
empty; `false` decides nothing. A bundle without members is the whole space, so answers `false`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.representsa_emptySet (zB : ZonoBundle (Vec 𝕋 n)) : Bool :=
  if hk : 0 < zB.k then (zB.conZonotopeAll hk).representsa_emptySet else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

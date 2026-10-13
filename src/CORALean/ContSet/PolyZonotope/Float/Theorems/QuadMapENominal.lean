module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE

@[expose] public section

/-!
# The exponent bookkeeping of `quadMap` is the same term in both layers

`quadMapE` is `rfl`-equal across the layers, being a sum of naturals either way.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exponent bookkeeping is the same term in both layers. -/
theorem PolyZonotope.quadMapE_nominal (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope.quadMapE pZ = Real.PolyZonotope.quadMapE (nominal pZ) := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact

/-!
# `compactFactors`'s nominal part is the exact layer's

Dropping unused factors is the exact layer's step verbatim: it changes `p` and
the exponent matrix, both over ℕ, so nothing here rounds.
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

/-- Dropping unused factors is the exact layer's step verbatim: the nominal part
of the result is `compactFactors` of the nominal part. -/
theorem PolyZonotope.compactFactors_nominal (pZ : PolyZonotope (Vec 𝕋 n)) :
    nominalSet pZ = nominalSet pZ.compactFactors :=
  Real.PolyZonotope.compactFactors_exact (InflatedContSet.nominal pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

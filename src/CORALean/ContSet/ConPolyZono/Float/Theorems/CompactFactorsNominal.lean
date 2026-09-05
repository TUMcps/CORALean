import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact

/-!
# `compactFactors`'s nominal part is the exact layer's

Costs nothing at all: it changes `p` and both exponent matrices, all over ℕ, so
the nominal part of the result *is* the exact layer's `compactFactors` of the
nominal part.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConPolyZono.compactFactors_nominal (C : ConPolyZono 𝕋 n) :
    nominalSet C = nominalSet C.compactFactors :=
  Real.ConPolyZono.compactFactors_exact (InflatedContSet.nominal C)

end CORALean.Float

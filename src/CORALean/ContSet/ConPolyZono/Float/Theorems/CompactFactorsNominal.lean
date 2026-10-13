import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsEqSpec
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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactFactors_nominal (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ = nominalSet cPZ.compactFactors := by
  rw [ConPolyZono.compactFactors_eq_spec]
  exact Real.ConPolyZono.compactFactors_exact (InflatedContSet.nominal cPZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

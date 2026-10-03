import CORALean.ContSet.Zonotope.Float.Operations.GeneratorLength
import CORALean.ContSet.Zonotope.Real.Operations.GeneratorLength

/-!
# The float generator length bounds the real one

The nominal zonotope's generator `j` has Euclidean length at most the rounded-up
`Zonotope.generatorLength`: an outer statement, the stored number is never below the length.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.generatorLength_le (k : ℕ) (Z : Zonotope 𝕋 n) (j : Fin Z.h) :
    (CORALean.Real.Zonotope.generatorLength (nominal Z) j : ℝ) ≤
      toReal (Z.generatorLength k j) := by
  exact norm₂_le_normUp k fun i => le_refl _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

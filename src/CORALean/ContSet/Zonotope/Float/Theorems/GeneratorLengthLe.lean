module

public import CORALean.ContSet.Zonotope.Float.Operations.GeneratorLength
public import CORALean.ContSet.Zonotope.Real.Operations.Basic

@[expose] public section

/-!
# The float generator length bounds the real one

The nominal zonotope's generator `j` has Euclidean length at most the rounded-up
`Zonotope.generatorLength`: an outer statement, the stored number is never below the length.

## Inputs
* `k` – Newton steps for the norm
* `Z` – zonotope
* `j` – generator index

## Hypotheses
* none

## Conclusion
* real length is at most the rounded-up length
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.generatorLength_le (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) :
    (CORALean.Real.Zonotope.generatorLength (nominal Z) j : ℝ) ≤
      toReal (Z.generatorLength k j) := by
  exact norm₂_le_normUp k fun i => le_refl _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

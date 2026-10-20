module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalSetDependent

@[expose] public section

/-!
# Making the independent generators dependent loses nothing here either

The float operation rounds nothing, so its whole content is `nominalSet_dependent`
and the error box is the same box.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is unchanged
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.dependent_exact (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct = cPZ.dependent.construct := by
  show nominalSet cPZ + (I_error cPZ).construct
    = nominalSet cPZ.dependent + (I_error cPZ.dependent).construct
  rw [ConPolyZono.nominalSet_dependent]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalSetDependent

/-!
# Making the independent generators dependent loses nothing here either

The float operation rounds nothing, so its whole content is `nominalSet_dependent`
and the error box is the same box.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.dependent_exact (C : ConPolyZono 𝕋 n) :
    C.construct = C.dependent.construct := by
  show nominalSet C + (error C).construct
    = nominalSet C.dependent + (error C.dependent).construct
  rw [ConPolyZono.nominalSet_dependent]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

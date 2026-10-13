module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalDependent
public import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact

@[expose] public section

/-!
# `dependent`'s nominal set is unchanged

`nominal_dependent` read into `construct`, then the exact layer's
`dependent_exact` closes it.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.nominalSet_dependent (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ.dependent = nominalSet cPZ := by
  show Real.ConPolyZono.construct (nominal cPZ.dependent)
    = Real.ConPolyZono.construct (nominal cPZ)
  rw [ConPolyZono.nominal_dependent, ← Real.ConPolyZono.dependent_exact]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

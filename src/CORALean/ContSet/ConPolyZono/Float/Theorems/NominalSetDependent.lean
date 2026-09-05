import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalDependent
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact

/-!
# `dependent`'s nominal set is unchanged

`nominal_dependent` read into `construct`, then the exact layer's
`dependent_exact` closes it.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem ConPolyZono.nominalSet_dependent (C : ConPolyZono 𝕋 n) :
    nominalSet C.dependent = nominalSet C := by
  show Real.ConPolyZono.construct (nominal C.dependent)
    = Real.ConPolyZono.construct (nominal C)
  rw [ConPolyZono.nominal_dependent, ← Real.ConPolyZono.dependent_exact]

end CORALean.Float

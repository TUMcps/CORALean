import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Theorems.AndDepOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.DependentExact

/-!
# `ConPolyZono.and` over-approximates the intersection

`andDep_outer` at the two dependent forms `and` builds its argument from, the
first intersection in this repository that a machine can run on non-convex
sets.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.and_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) :
    cPZ₁.construct ∩ cPZ₂.construct ⊆ (cPZ₁.and cPZ₂).construct := by
  rw [cPZ₁.dependent_exact, cPZ₂.dependent_exact]
  exact ConPolyZono.andDep_outer cPZ₁.dependent cPZ₂.dependent rfl rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

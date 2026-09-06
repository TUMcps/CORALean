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

theorem ConPolyZono.and_outer (C₁ C₂ : ConPolyZono 𝕋 n) :
    C₁.construct ∩ C₂.construct ⊆ (C₁.and C₂).construct := by
  rw [C₁.dependent_exact, C₂.dependent_exact]
  exact ConPolyZono.andDep_outer C₁.dependent C₂.dependent rfl rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

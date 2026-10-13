module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionDepOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.DependentExact

@[expose] public section

/-!
# `ConPolyZono.intersection` over-approximates the intersection

`intersectionDep_outer` at the two dependent forms `intersection` builds its argument from, the
first intersection in this repository that a machine can run on non-convex
sets.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.intersection_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ₁.construct ∩ cPZ₂.construct ⊆ (cPZ₁.intersection cPZ₂).construct := by
  rw [cPZ₁.dependent_exact, cPZ₂.dependent_exact]
  exact ConPolyZono.intersectionDep_outer cPZ₁.dependent cPZ₂.dependent rfl rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

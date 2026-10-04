import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage

/-!
# A constrained zonotope is empty iff its coefficient polytope is
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.representsa_emptySet_iff (cZ : ConZonotope α) :
    cZ.construct = ∅ ↔ cZ.representsa_emptySet := by
  rw [ConZonotope.construct_eq_image, ConZonotope.representsa_emptySet]
  exact Set.image_eq_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

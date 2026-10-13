module

public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage

@[expose] public section

/-!
# A constrained zonotope is empty iff its coefficient polytope is
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

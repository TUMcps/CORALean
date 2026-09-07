import CORALean.ContSet.ConZonotope.Real.Operations.Domain
import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
import CORALean.ContSet.HPolytope.Real.Operations.MemUnitBoxIff

/-!
# Membership in `ConZonotope.domain`
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem ConZonotope.mem_domain_iff {cZ : ConZonotope α} {β : Vec ℝ cZ.h} :
    β ∈ cZ.domain.construct ↔ (∀ j, |β j| ≤ 1) ∧ β ∈ cZ.P.construct := by
  have hand : β ∈ cZ.domain.construct ↔ β ∈ (HPolytope.unitBox cZ.h).construct
      ∧ β ∈ cZ.P.construct := HPolytope.mem_intersection_iff
  rw [hand, HPolytope.mem_unitBox_iff]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

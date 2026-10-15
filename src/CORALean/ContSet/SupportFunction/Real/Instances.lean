module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.SupportFunction.Real.Theorems.Convex

@[expose] public section

/-!
# What `SupportFunction` instantiates

`ContSet` and `ConvexSet`. Nothing else: no operation is closed form on a function of all
functionals but the sum, the linear map and the convex hull of the sets it stands for, which the
support function algorithms of `ContDynamics` apply to the sets directly.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  INSTANCES  ========================================= --

instance {α : Type} [AddCommGroup α] [Module ℝ α] :
    ContSet (SupportFunction α) α := ⟨SupportFunction.construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ConvexSet (SupportFunction α) α :=
  ⟨SupportFunction.convex_construct⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

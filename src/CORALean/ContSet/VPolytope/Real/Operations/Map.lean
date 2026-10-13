import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `VPolytope.map`

A linear map applies to the vertices, the count untouched, exactly as it does to
a zonotope's centre and generators. Every multiplication a vertex description
carries is this at a particular map.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.map (f : α →ₗ[ℝ] β) (P : VPolytope α) : VPolytope β where
  k := P.k
  V := fun j => f (P.V j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

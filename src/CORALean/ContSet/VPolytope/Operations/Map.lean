import CORALean.ContSet.VPolytope.VPolytope

/-!
# `VPolytope.map`

A linear map applies to the vertices, the count untouched, exactly as it does to
a zonotope's centre and generators. Every multiplication a vertex description
carries is this at a particular map.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

def VPolytope.map (f : α →ₗ[ℝ] β) (P : VPolytope α) : VPolytope β where
  k := P.k
  V := fun j => f (P.V j)

end CORALean.Real

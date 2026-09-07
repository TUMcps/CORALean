import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# `ZonoBundle.map`

A linear map applied to every zonotope in the family, the count `k` untouched:
`construct` reads only the family, so moving each member is all a bundle needs
to move.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.map (f : α →ₗ[ℝ] β) (zB : ZonoBundle α) : ZonoBundle β where
  k := zB.k
  Z := fun i => Zonotope.map f (zB.Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

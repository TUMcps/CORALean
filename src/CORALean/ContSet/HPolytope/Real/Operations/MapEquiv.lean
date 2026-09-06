import CORALean.ContSet.HPolytope.Real.Operations.Comap

/-!
# `HPolytope.mapEquiv`

The image under an invertible linear map, which is the preimage under its
inverse. Exact, and this is what CORA's `mtimes` on a halfspace description
amounts to: a general matrix would need the image of a polytope, which is a
projection and so vertex enumeration, but an invertible one costs nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.mapEquiv (e : α ≃ₗ[ℝ] β) (P : HPolytope α) : HPolytope β :=
  P.comap (e.symm : β →ₗ[ℝ] α)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

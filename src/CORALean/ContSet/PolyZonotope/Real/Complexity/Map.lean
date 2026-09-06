import CORALean.ContSet.PolyZonotope.Real.Operations.Map

/-!
# `PolyZonotope.map`'s counts

A linear map touches the centre and both generator blocks only: none of the
three counts move, since the monomials are scalars a linear map commutes with.
`rfl` against the structure instance in `Operations/Map.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.map_p (f : α →ₗ[ℝ] β) (PZ : PolyZonotope α) :
    (PolyZonotope.map f PZ).p = PZ.p := rfl

theorem PolyZonotope.map_h (f : α →ₗ[ℝ] β) (PZ : PolyZonotope α) :
    (PolyZonotope.map f PZ).h = PZ.h := rfl

theorem PolyZonotope.map_q (f : α →ₗ[ℝ] β) (PZ : PolyZonotope α) :
    (PolyZonotope.map f PZ).q = PZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

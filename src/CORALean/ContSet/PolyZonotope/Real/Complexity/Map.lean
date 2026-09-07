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

theorem PolyZonotope.map_p (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    (PolyZonotope.map f pZ).p = pZ.p := rfl

theorem PolyZonotope.map_h (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    (PolyZonotope.map f pZ).h = pZ.h := rfl

theorem PolyZonotope.map_q (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    (PolyZonotope.map f pZ).q = pZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

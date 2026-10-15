module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map

@[expose] public section

/-!
# `PolyZonotope.map`'s counts

A linear map touches the center and both generator blocks only: none of the
three counts move, since the monomials are scalars a linear map commutes with.
`rfl` against the structure instance in `Operations/Map.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `map`'s result. -/
theorem PolyZonotope.map_p (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α) :
    (PolyZonotope.map f pZ).p = pZ.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

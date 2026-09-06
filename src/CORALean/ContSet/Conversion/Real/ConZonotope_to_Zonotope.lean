import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# Dropping the constraints

CORA's `zonotope(conZonotope)` in its cheapest form: forget what the
coefficients had to satisfy and keep the generators. Enclosing rather than
exact, and by exactly the constraints thrown away.

Every other route out of a constrained zonotope goes through a linear program on
its coefficient domain; this one is free, and is what `reduce` and `linComb`
fall back on.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.zonotope (C : ConZonotope α) : Zonotope α where
  h := C.h
  c := C.c
  G := C.G


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zonotope_outer (C : ConZonotope α) : C.construct ⊆ C.zonotope.construct := by
  rintro _ ⟨β, hβ, -, rfl⟩
  exact ⟨β, hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

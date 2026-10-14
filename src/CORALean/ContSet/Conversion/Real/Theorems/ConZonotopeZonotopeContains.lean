module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# Dropping the constraints

CORA's `zonotope(conZonotope)` in its cheapest form: forget what the
coefficients had to satisfy and keep the generators. Enclosing rather than
exact, and by exactly the constraints thrown away.

Every other route out of a constrained zonotope goes through a linear program on
its coefficient domain; this one is free, and is what `reduce` and `linComb`
fall back on.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zonotope_contains (cZ : ConZonotope α) :
    cZ.construct ⊆ cZ.zonotope.construct := by
  rintro _ ⟨β, hβ, -, rfl⟩
  exact ⟨β, hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

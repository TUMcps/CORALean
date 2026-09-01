import CORALean.ContSet.ConZonotope.Operations.Zonotope

/-!
# Forgetting the constraints encloses, adding none loses nothing

The same coefficients witness both: dropping `A β = b` admits more of them, and
a constraint block with no rows admits all of them.

Everything a constrained zonotope gives up goes through the first of these, so
`linComb` and `reduce` are enclosures by composing with it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem ConZonotope.zonotope_outer (C : ConZonotope α) : C.construct ⊆ C.zonotope.construct := by
  rintro _ ⟨β, hβ, -, rfl⟩
  exact ⟨β, hβ, rfl⟩

theorem Zonotope.conZonotope_exact (Z : Zonotope α) : Z.construct = Z.conZonotope.construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, funext fun i => i.elim0, rfl⟩
  · rintro _ ⟨β, hβ, -, rfl⟩
    exact ⟨β, hβ, rfl⟩

end CORALean.Real

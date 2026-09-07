import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

/-!
# A zonotope is a constrained one with nothing to satisfy

Exact, and the reason a constrained zonotope needs no separate treatment of the
unconstrained case: `fullspace` is the unit of the coefficient domain's `intersection`,
so the empty constraint list denotes the whole coefficient space.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def Zonotope.conZonotope (Z : Zonotope α) : ConZonotope α where
  h := Z.h
  c := Z.c
  G := Z.G
  P := HPolytope.fullspace _


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.conZonotope_exact (Z : Zonotope α) :
    Z.construct = Z.conZonotope.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, ⟨fun i => i.elim0, fun i => i.elim0⟩, rfl⟩
  · rintro _ ⟨β, hβ, -, rfl⟩
    exact ⟨β, hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

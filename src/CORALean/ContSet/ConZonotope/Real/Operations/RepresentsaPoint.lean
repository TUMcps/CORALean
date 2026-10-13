module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain

@[expose] public section

/-!
# `ConZonotope.representsa_point`

CORA's `@conZonotope/representsa_` at type `point`: `representsa_(interval(cZ),'point',tol)`, the
(linear-program tight) interval hull of the set is a point, at tolerance `0`. The hull is a point
exactly when the generator map `ξ ↦ G ξ` is constant on the coefficient polytope
`ConZonotope.domain`, and the polytope is nonempty (CORA returns `[]` for an empty set).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conZonotope/representsa_` at `point`: `G` is constant on a nonempty coefficient polytope. -/
def ConZonotope.representsa_point (cZ : ConZonotope α) : Prop :=
  ∃ β₀ ∈ cZ.domain.construct, ∀ β ∈ cZ.domain.construct,
    ∑ j, β j • cZ.G j = ∑ j, β₀ j • cZ.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

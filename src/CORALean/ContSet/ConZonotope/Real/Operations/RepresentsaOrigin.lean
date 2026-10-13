module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain

@[expose] public section

/-!
# `ConZonotope.representsa_origin`

CORA's `@conZonotope/representsa_` at type `origin`: `representsa_(interval(cZ),'origin',tol)`,
the interval hull is the point `0`, at tolerance `0`: the set is a point (see `representsa_point`)
and the point is `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conZonotope/representsa_` at `origin`. -/
def ConZonotope.representsa_origin (cZ : ConZonotope α) : Prop :=
  ∃ β₀ ∈ cZ.domain.construct, cZ.c + ∑ j, β₀ j • cZ.G j = 0 ∧ ∀ β ∈ cZ.domain.construct,
    ∑ j, β j • cZ.G j = ∑ j, β₀ j • cZ.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

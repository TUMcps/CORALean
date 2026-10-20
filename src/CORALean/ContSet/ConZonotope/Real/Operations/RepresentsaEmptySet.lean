module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain

@[expose] public section

/-!
# `ConZonotope.representsa_emptySet`

CORA's `@conZonotope/representsa_` at type `emptySet` (`aux_isEmptySet`): the zonotope `(c, G)`
is never empty, so without constraints the answer is `false`; otherwise `representsa` of the
polytope `[-1, 1]^m ∩ {A ξ = b}`, which CORA decides by a linear program. The coefficient
polytope is `ConZonotope.domain`.

## Inputs
* `cZ` – constrained zonotope

## Output
* the set is empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conZonotope/representsa_` at `emptySet`: the coefficient polytope has no point. -/
def ConZonotope.representsa_emptySet (cZ : ConZonotope α) : Prop := cZ.domain.construct = ∅

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

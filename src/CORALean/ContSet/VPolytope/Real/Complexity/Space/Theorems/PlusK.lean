module

public import CORALean.ContSet.VPolytope.Real.Operations.Plus

@[expose] public section

/-!
# `VPolytope.plus_k`

`plus`'s vertex count: every vertex of one operand paired with every vertex of
the other, so the count multiplies rather than adds — the one place a vertex
description costs more than a zonotope's. `rfl`, since `Operations/Plus.lean`
states `k` directly in the structure instance.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
/-- The `k` count of `plus`'s result. -/
theorem VPolytope.plus_k (P₁ P₂ : VPolytope α) : (P₁.plus P₂).k = P₁.k * P₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

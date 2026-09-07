import CORALean.ContSet.VPolytope.Real.Operations.Plus

/-!
# `VPolytope.plus_k`

`plus`'s vertex count: every vertex of one operand paired with every vertex of
the other, so the count multiplies rather than adds — the one place a vertex
description costs more than a zonotope's. `rfl`, since `Operations/Plus.lean`
states `k` directly in the structure instance.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem VPolytope.plus_k (P₁ P₂ : VPolytope α) : (P₁.plus P₂).k = P₁.k * P₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

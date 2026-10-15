module

public import CORALean.ContSet.VPolytope.Real.Operations.LinComb

@[expose] public section

/-!
# `VPolytope.linComb_k`

`linComb`'s vertex count: the two vertex lists concatenated, with no fresh
vertex needed the way a zonotope needs a fresh generator — a vertex list
already denotes the convex hull of its union. `rfl`, since
`Operations/LinComb.lean` states `k` directly.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
/-- The `k` count of `linComb`'s result. -/
theorem VPolytope.linComb_k (P₁ P₂ : VPolytope α) : (P₁.linComb P₂).k = P₁.k + P₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

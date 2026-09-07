import CORALean.ContSet.VPolytope.Real.Operations.LinComb

/-!
# `VPolytope.linComb_k`

`linComb`'s vertex count: the two vertex lists concatenated, with no fresh
vertex needed the way a zonotope needs a fresh generator — a vertex list
already denotes the convex hull of its union. `rfl`, since
`Operations/LinComb.lean` states `k` directly.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem VPolytope.linComb_k (P₁ P₂ : VPolytope α) : (P₁.linComb P₂).k = P₁.k + P₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

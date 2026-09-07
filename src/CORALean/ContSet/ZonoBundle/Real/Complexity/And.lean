import CORALean.ContSet.ZonoBundle.Real.Operations.And

/-!
# `ZonoBundle.and_k`

`and`'s bundle size: the two families appended, one bundle's zonotopes
alongside the other's, so the count adds and every component passes through
untouched. `rfl`, since `Operations/And.lean` states `k` directly in the
structure instance.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] in
theorem ZonoBundle.and_k (B₁ B₂ : ZonoBundle α) : (B₁.and B₂).k = B₁.k + B₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

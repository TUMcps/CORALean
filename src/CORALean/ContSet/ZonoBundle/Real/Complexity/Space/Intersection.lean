module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection

@[expose] public section

/-!
# `ZonoBundle.intersection_k`

`intersection`'s bundle size: the two families appended, one bundle's zonotopes
alongside the other's, so the count adds and every component passes through
untouched. `rfl`, since `Operations/Intersection.lean` states `k` directly in the
structure instance.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] in
theorem ZonoBundle.intersection_k (zB₁ zB₂ : ZonoBundle α) :
    (zB₁.intersection zB₂).k = zB₁.k + zB₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

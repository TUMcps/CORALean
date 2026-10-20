module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ZonoBundle.plus`'s counts

`plus`'s bundle size: every zonotope of one bundle paired with every zonotope of the other, so the
count multiplies rather than adds, the reason it, not `intersection`, carries this directory's
`O`-notation statement, in `PlusKIsBigO.lean`. The second-order count comes out cleanly: each paired
component is `Zonotope.plus` of the two it came from, so its generator count is theirs added, by
`Zonotope.plus_h` (`rfl`). The bundle size is `O(m ^ 2)`, tied to `plus` through a family of bundles
whose sizes grow as `m`: `plus_k` reduces the left side to `m * m`, which `m ^ 2` dominates.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
/-- The `k` count of `plus`'s result. -/
theorem ZonoBundle.plus_k (zB₁ zB₂ : ZonoBundle α) : (zB₁.plus zB₂).k = zB₁.k * zB₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

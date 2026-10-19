module

public import CORALean.ContSet.VPolytope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `VPolytope.bilin_k`

`bilin`'s vertex count: every vertex of `P` paired with every vertex of `Q`, so the count is their
product outright, not a sum plus a cross block the way `Zonotope.bilin_h` is — a vertex description
has no linear part to keep separate from the pairing. `rfl`, since `Operations/Bilin.lean` states
`k` directly. `BilinKIsBigO.lean` puts this in `O`-notation: the count is `O(m ^ 2)`.

## Inputs
* `f` – bilinear map
* `P` – first polytope
* `Q` – second polytope

## Hypotheses
* none

## Conclusion
* the vertex count of `bilin f P Q` is `P.k * Q.k`
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `k` count of `bilin`'s result. -/
theorem VPolytope.bilin_k (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (P : VPolytope α) (Q : VPolytope β) :
    (VPolytope.bilin f P Q).k = P.k * Q.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

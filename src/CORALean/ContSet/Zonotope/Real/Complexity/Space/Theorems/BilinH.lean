module

public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `Zonotope.bilin_h`

`bilin`'s generator count: each operand's own, plus the cross block at their
product — quadratic, not linear, in the operands' sizes. `rfl`, since
`Operations/Bilin.lean` states `h` directly. `BilinHIsBigO.lean` puts this in
`O`-notation, along a family of operands whose sizes grow.

## `bilin`'s cost is `O(m ^ 2)`

The shape the rest of `Complexity/Space/` should eventually take: not a bare
arithmetic fact about `m + m + m * m`, but one tied to `bilin` through a family
of zonotopes whose sizes grow as `m`. `bilin_h` reduces the left side to that
sum, which `3 * m ^ 2` dominates for every `m`, so the bound needs no filter
condition — `IsBigO.of_bound` still asks for one only eventually.

`Asymptotics.IsBigO.of_bound` closes it: it asks for domination by a fixed
constant `∀ᶠ x in l`, which the whole range `m ≥ 1` clears with room to spare.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `bilin`'s result. -/
theorem Zonotope.bilin_h (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (Z₁ : Zonotope α) (Z₂ : Zonotope β) :
    (Zonotope.bilin f Z₁ Z₂).h = Z₁.h + Z₂.h + Z₁.h * Z₂.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

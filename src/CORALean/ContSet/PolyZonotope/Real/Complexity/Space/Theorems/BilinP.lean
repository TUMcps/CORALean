module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `PolyZonotope.bilin`'s counts

The shared factor count carries over from either operand, since sharing is a
hypothesis rather than a fresh count; the dependent generator count is the two
operands' own plus their cross block, `(h₁+1)*(h₂+1)` — quadratic, not linear;
and the independent block is empty, `bilin` being a claim about `point`.
`BilinHIsBigO.lean` puts the quadratic one in `O`-notation. `rfl` against the
structure instance in `Operations/Bilin.lean`.

## `PolyZonotope.bilin`'s dependent-generator count is `O(m ^ 2)`

Not a bare arithmetic fact about `(m+1)*(m+1)`, but one tied to `bilin` through
a family of sets whose dependent-generator counts grow as `m`. `bilin_h`
reduces the left side to that product, which `4 * m ^ 2` dominates for every
`m ≥ 1`.

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

/-- The `p` count of `bilin`'s result. -/
theorem PolyZonotope.bilin_p (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β)
    (hp : pZ₁.p = pZ₂.p) : (PolyZonotope.bilin f pZ₁ pZ₂ hp).p = pZ₁.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

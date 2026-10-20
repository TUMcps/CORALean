module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `PolyZonotope.bilin`'s counts

The shared factor count carries over from either operand, sharing being a hypothesis; the
dependent generator count is the cross block `(h₁+1)*(h₂+1)`, quadratic not linear; and the
independent block is empty, `bilin` being a claim about `point`. `rfl` against the structure
instance in `Operations/Bilin.lean`. `BilinHIsBigO.lean` puts the quadratic count in
`O`-notation: `bilin_h` reduces it to that product, which `4 * m ^ 2` dominates for every
`m ≥ 1`, closed by `Asymptotics.IsBigO.of_bound`.

## Inputs
* `f` – bilinear map
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the factor count is preserved
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

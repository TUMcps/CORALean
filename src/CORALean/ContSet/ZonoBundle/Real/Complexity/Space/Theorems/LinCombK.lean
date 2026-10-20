module

public import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.Basic

@[expose] public section

/-!
# `ZonoBundle.linComb`'s counts

`linComb`'s bundle size: every zonotope of one bundle paired with every
zonotope of the other, so the count multiplies exactly as `plus`'s does.

The second-order count also comes out cleanly: each paired component is
`Zonotope.linComb` of the two it came from, so its own generator count is
theirs added plus the one fresh generator, by `Zonotope.linComb_h`. `rfl`
against both structure instances.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* none

## Conclusion
* the hull has the product of the member counts
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `k` count of `linComb`'s result. -/
theorem ZonoBundle.linComb_k (zB₁ zB₂ : ZonoBundle α) : (zB₁.linComb zB₂).k = zB₁.k * zB₂.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

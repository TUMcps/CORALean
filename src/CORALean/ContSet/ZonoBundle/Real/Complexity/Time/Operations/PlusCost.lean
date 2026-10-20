module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `ZonoBundle.plusCost`

Asserted, not proved: `Operations/Plus.lean` runs `Zonotope.plus` once per pair
of members, `k₁ * k₂` of them, and does nothing of its own; the sums write their own results, inside
`Zonotope.plusCost`.

The product is the whole point of the count. A bundle sum is not a bundle of sums: each member of
one has to be added to each member of the other for the intersection to be an enclosure, so where a
zonotope's `plus` is `n` additions, a bundle's is `k₁ * k₂ * n`, and two sums in a row square that
again. `Complexity/Space/Theorems/Plus*.lean` is the same fact about the *size* of the result.

## Inputs
* `n` – dimension
* `k₁` – members of the first bundle
* `k₂` – members of the second bundle
* `h₁` – generators per member of the first
* `h₂` – generators per member of the second

## Output
* the cost of the Minkowski sum
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.plus` costs at `Vec ℝ n` on bundles of `k₁` and `k₂` members, none over `h₁`
and `h₂` generators: one zonotope sum per pair. -/
def ZonoBundle.plusCost (n k₁ k₂ h₁ h₂ : ℕ) : Cost := (k₁ * k₂) • Zonotope.plusCost n h₁ h₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

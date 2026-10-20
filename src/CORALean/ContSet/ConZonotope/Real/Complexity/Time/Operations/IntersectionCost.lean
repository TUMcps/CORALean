module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.Global.Cost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.ComapCost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.IntersectionCost

@[expose] public section

/-!
# `ConZonotope.intersectionCost`

Asserted, not proved: `Operations/Intersection.lean` keeps the first center and generator block
and adds the equalities `G₁ β₁ - G₂ β₂ = c₂ - c₁`. Assembling `aux_agreeMat` negates the `n * h₂`
entries of the second block; the right-hand side is `n` subtractions.

Everything is written: the center and the `h₁ + h₂` generators of `n` entries, the second block's
padding zeros included. The polytope is two `comap`s and an `intersection` as in `plus`, the `n`
equality rows of `aux_agreeMat` with their right-hand sides (`n * (h₁ + h₂ + 1)` writes, rows
dense), and a second `intersection` adding them.

## Inputs
* `n` – dimension
* `h₁` – generators of the first set
* `h₂` – generators of the second set
* `r₁` – inequalities of the first set
* `re₁` – equalities of the first set
* `r₂` – inequalities of the second set
* `re₂` – equalities of the second set

## Output
* the cost of the intersection
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.intersection` costs at `Vec ℝ n`, `hᵢ` generators and a constraint polytope
of `rᵢ` inequality and `reᵢ` equality rows each: the negations and subtractions of the agreement
rows, and the writes of the zonotope and the polytope. -/
def ConZonotope.intersectionCost (n h₁ h₂ r₁ re₁ r₂ re₂ : ℕ) : Cost :=
  ⟨n * (h₂ + 1) + n * (1 + h₁ + h₂) + n * (h₁ + h₂ + 1)⟩ +
    HPolytope.comapCost r₁ re₁ ⟨h₁ + h₂ + 1⟩ + HPolytope.comapCost r₂ re₂ ⟨h₁ + h₂ + 1⟩ +
    HPolytope.intersectionCost (h₁ + h₂) r₁ r₂ re₁ re₂ +
    HPolytope.intersectionCost (h₁ + h₂) (r₁ + r₂) n (re₁ + re₂) 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

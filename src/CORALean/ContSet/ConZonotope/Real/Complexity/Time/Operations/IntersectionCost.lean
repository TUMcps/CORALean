module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConZonotope.intersectionCost`

Asserted, not proved: `Operations/Intersection.lean` keeps the first center and
generator block, pads the second block with zeros, builds the polytope as in
`plus` (free) and adds the equalities `G₁ β₁ - G₂ β₂ = c₂ - c₁`. Assembling
`agreeMat` negates the `n * h₂` entries of the second block, and the right-hand
side is `n` subtractions; `HPolytope.eqs` wraps the rows as functionals and is
free. No linear program is solved: emptiness is not decided here.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.intersection` costs at `Vec ℝ n` and `h₂` generators in the
second operand: `n * h₂` negations and `n` subtractions. -/
def ConZonotope.intersectionCost (n h₂ : ℕ) : Cost := ⟨n * (h₂ + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

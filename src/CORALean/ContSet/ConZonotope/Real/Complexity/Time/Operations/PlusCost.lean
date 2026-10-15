module

public import CORALean.ContSet.ConZonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.ComapCost
public import CORALean.ContSet.HPolytope.Real.Complexity.Time.Operations.IntersectionCost

@[expose] public section

/-!
# `ConZonotope.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the centers, as `Zonotope.plus` does, and builds
the polytope from two `comap`s along the block embeddings `blockLeft` and `blockRight` and one
`intersection`. A block embedding copies a row into a longer one, `h₁ + h₂ + 1` entries with its
right-hand side, which `HPolytope.comapCost` charges as the writes of the row. The count is
`Zonotope.plusCost`, the two `comap`s and the `intersection`'s writes, rows read dense.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.plus` costs at `Vec ℝ n`, `hᵢ` generators and a constraint polytope of `rᵢ`
inequality and `reᵢ` equality rows each: the zonotope's sum, the two block `comap`s and the
`intersection` of their results. -/
def ConZonotope.plusCost (n h₁ h₂ r₁ re₁ r₂ re₂ : ℕ) : Cost :=
  Zonotope.plusCost n h₁ h₂ + HPolytope.comapCost r₁ re₁ ⟨h₁ + h₂ + 1⟩ +
    HPolytope.comapCost r₂ re₂ ⟨h₁ + h₂ + 1⟩ + HPolytope.intersectionCost (h₁ + h₂) r₁ r₂ re₁ re₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

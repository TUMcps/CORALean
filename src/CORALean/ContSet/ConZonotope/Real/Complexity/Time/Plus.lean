import CORALean.ContSet.ConZonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Plus

/-!
# `ConZonotope.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the centres, as
`Zonotope.plus` does, and builds the polytope from two `comap`s along the block
embeddings `blockLeft` and `blockRight` and one `intersection`. A block
embedding copies a row into a longer one, so `HPolytope.comapCost` at zero
applies, and `HPolytope.intersectionCost` is zero too: the whole count is the
centre's `n` additions, however many constraints the operands carry.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.plus` costs at `Vec ℝ n`: the centre's `n` additions, the
two block `comap`s and the `intersection` being free. The same count as
`Zonotope.plusCost`: constraints are carried along at no price. -/
def ConZonotope.plusCost (n : ℕ) : Cost := Zonotope.plusCost n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

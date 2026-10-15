module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapDepCost

@[expose] public section

/-!
# `ConPolyZono.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` is `quadMapDep` after
`dependent`, and `quadMapDep`'s own generators and exponent matrix are exactly
`PolyZonotope.quadMapDep`'s, run on the enclosing polynomial zonotope — the
constraint system passes through untouched. So the whole count is
`PolyZonotope.quadMapDepCost` at the sizes `dependent` leaves: `p + qI` factors
and `h + qI` dependent generators, both proved in `Complexity/Space/Theorems/QuadMap*.lean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.quadMap` costs at `m` matrices of size `n × n`: the
polynomial-zonotope quadratic map at the counts `dependent` leaves, the
conversion itself free. -/
def ConPolyZono.quadMapCost (m n p h qI : ℕ) : Cost :=
  ConPolyZono.dependentCost + PolyZonotope.quadMapDepCost m n (p + qI) (h + qI)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

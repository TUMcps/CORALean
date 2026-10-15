module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapDepCost

@[expose] public section

/-!
# `ConPolyZono.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` is `quadMapDep` after `dependent`, and
`quadMapDep`'s own generators and exponent matrix are exactly `PolyZonotope.quadMapDep`'s, run on
the enclosing polynomial zonotope, read off the dependent set by a conversion that writes its
`n * (1 + (h + qI)) + (p + qI) * (h + qI)` scalars. The constraint system passes through, but its
entries are part of the result and are written. So the count is `dependentCost`,
`PolyZonotope.quadMapDepCost` at the sizes `dependent` leaves, `p + qI` factors and `h + qI`
dependent generators, both proved in `Complexity/Space/Theorems/QuadMap*.lean`, and those writes.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.quadMap` costs at `m` matrices of size `n × n` on `p` factors, `h`, `qI`
generators, `mC` constraints over `q`: the conversion, the map at the counts it leaves, and the
writes of the constraint block and of the polynomial zonotope read off the dependent set. -/
def ConPolyZono.quadMapCost (m n p h qI mC q : ℕ) : Cost :=
  ConPolyZono.dependentCost n p h qI mC q + PolyZonotope.quadMapDepCost m n (p + qI) (h + qI) +
    ⟨mC * q + 2 * mC + (p + qI) * q + (n * (1 + (h + qI)) + (p + qI) * (h + qI))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

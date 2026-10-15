module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapDepCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

@[expose] public section

/-!
# `PolyZonotope.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` is `quadMapDep` after
`dependent`, and `dependentCost` is zero, so the whole count is `quadMapDepCost`
at the sizes `dependent` leaves — `p + q` factors and `h + q` dependent
generators, both proved in `Complexity/Space/Theorems/DependentP.lean`.

That the independent generators enter the *square* is the operation's own
doing and the reason a caller reduces before mapping rather than after: `q`
free coefficients cost `q` dependent generators here, and `(h+q)²` pairs after
that.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.quadMap` costs at `m` matrices of size `n × n`: the
dependent map at the counts `dependent` leaves, the conversion itself free. -/
def PolyZonotope.quadMapCost (m n p h q : ℕ) : Cost :=
  PolyZonotope.dependentCost + PolyZonotope.quadMapDepCost m n (p + q) (h + q)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

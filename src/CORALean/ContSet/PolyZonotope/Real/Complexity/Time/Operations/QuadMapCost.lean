module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.QuadMapDepCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

@[expose] public section

/-!
# `PolyZonotope.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` is `quadMapDep` after `dependent`, so the count
is `dependentCost`, the conversion's writes, and `quadMapDepCost` at the sizes `dependent`
leaves, `p + q` factors and `h + q` dependent generators (`Space/Theorems/DependentP.lean`).
That the independent generators enter the *square* is why a caller reduces before mapping:
`q` free coefficients cost `q` dependent generators here, and `(h+q)²` pairs after that.

## Inputs
* `m` – output dimension
* `n` – input dimension
* `p` – number of factors
* `h` – dependent generator count
* `q` – independent generator count

## Output
* operation count of the quadratic map
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.quadMap` costs at `m` matrices of size `n × n`: the conversion, and the
dependent map at the counts `dependent` leaves. -/
def PolyZonotope.quadMapCost (m n p h q : ℕ) : Cost :=
  PolyZonotope.dependentCost n p h q + PolyZonotope.quadMapDepCost m n (p + q) (h + q)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

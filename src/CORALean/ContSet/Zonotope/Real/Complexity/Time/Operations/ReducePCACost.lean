module

public import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByBasisCost

@[expose] public section

/-!
# `Zonotope.reducePCACost`

Asserted, not proved, by reading `Operations/ReducePCA.lean`. Girard's partition
as in `reduceGirardCost` (metrics and sort); the scatter matrix `G Gᵀ` of the
dropped block, `n * n` entries of `2 * r` operations, bounded at `r = h`; the
eigendecomposition behind `pcaBasis`, which the definition takes from Mathlib's
`eigenvectorUnitary` and so fixes no algorithm for — its price `eig` is a
parameter, as is the inverse's inside `reduceByBasisCost`. A caller who runs a
dense symmetric solver would pass an `O(n^3)` count for each. At order `o`
or below the operation is the identity, so this bounds every `o` at once.

`reduceByBasis` writes its own result and is charged at `h` kept and `h` absorbed generators.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reducePCA` costs at `Vec ℝ n` on `h` generators, the eigendecomposition costing
at most `eig` and the basis inverse at most `inv`. -/
def Zonotope.reducePCACost (n h : ℕ) (eig inv : Cost) : Cost :=
  ⟨h * (4 * n + 2)⟩ + Cost.sort h + ⟨2 * (n * n * h)⟩ + eig + Zonotope.reduceByBasisCost n h h inv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

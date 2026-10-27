module

public import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.reducePCACost`

Asserted, not proved, by reading `Operations/ReducePCA.lean`. Girard's partition as in
`reduceGirardCost` (metrics and sort); the scatter matrix `G Gᵀ` of the dropped block, `n * n`
entries of `2 * r` operations, bounded at `r = h`; the eigendecomposition behind `pcaBasis`, which
Mathlib's `eigenvectorUnitary` fixes no algorithm for — its price `eig` is a parameter, as is the
inverse's inside `step_reduceByBasisCost`. At order `o` or below the operation is the identity, so
this bounds every `o` at once. `reduceByBasis` writes its own result.

## Inputs
* `n` – dimension
* `h` – generator count
* `eig` – cost of the eigendecomposition
* `inv` – cost of the basis inverse

## Output
* cost of PCA reduction
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- What `Zonotope.reduceByBasis` costs at `Vec ℝ n` keeping `q` and absorbing `r` generators,
the inverse costing at most `inv`: the `r` products with it, `2 * n * r + n * n` for the new
generators, and `n * (1 + q + n)` writes. -/
@[step_of Zonotope.reducePCACost]
def Zonotope.step_reduceByBasisCost (n q r : ℕ) (inv : Cost) : Cost :=
  inv + r • Cost.matVec n n + ⟨2 * (n * r) + n * n + n * (1 + q + n)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reducePCA` costs at `Vec ℝ n` on `h` generators, the eigendecomposition costing
at most `eig` and the basis inverse at most `inv`. -/
def Zonotope.reducePCACost (n h : ℕ) (eig inv : Cost) : Cost :=
  ⟨h * (4 * n + 2)⟩ + Cost.sort h + ⟨2 * (n * n * h)⟩ + eig + Zonotope.step_reduceByBasisCost n h h
    inv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceByCost

@[expose] public section

/-!
# `Zonotope.reduceByBasisCost`

Asserted, not proved: `Operations/ReduceByBasis.lean` inverts the basis `P`, a
numerical routine the definition names only as `P⁻¹`, so its price `inv` is a
parameter, as `mapCost` takes what one application of `f` costs. Then each of
the `r` absorbed generators goes through `P⁻¹ *ᵥ ·` (`Cost.matVec n n`), each
of the `n` output rows sums `r` absolute values (`2 * n * r`), and each column
of `P` is scaled by its sum (`n * n`).

The result is the center, the `q` kept generators and the `n * n` new ones, `n * (1 + q + n)`
writes; the `n * n` scalings are computed entries, so they are counted twice, once as arithmetic
and once as the write of the entry.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceByBasis` costs at `Vec ℝ n` keeping `q` and absorbing `r` generators,
the inverse costing at most `inv`: the `r` products with it, `2 * n * r + n * n` for the new
generators, and `n * (1 + q + n)` writes. -/
def Zonotope.reduceByBasisCost (n q r : ℕ) (inv : Cost) : Cost :=
  inv + r • Cost.matVec n n + ⟨2 * (n * r) + n * n + n * (1 + q + n)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

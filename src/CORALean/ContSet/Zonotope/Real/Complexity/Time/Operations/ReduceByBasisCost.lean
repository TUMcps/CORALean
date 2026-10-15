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
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceByBasis` costs at `Vec ℝ n` absorbing `r` generators,
the inverse costing at most `inv`. -/
def Zonotope.reduceByBasisCost (n r : ℕ) (inv : Cost) : Cost :=
  inv + r • Cost.matVec n n + ⟨2 * (n * r) + n * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

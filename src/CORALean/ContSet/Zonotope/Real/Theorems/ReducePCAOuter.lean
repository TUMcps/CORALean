module

public import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
public import CORALean.ContSet.Zonotope.Real.Theorems.PCABasisIsUnitDet
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter

@[expose] public section

/-!
# `pca` over-approximates

Two cases [1, Alg. 2], as Girard's rule and Combastel's have and `methC` does not: above the
order the basis is the principal axes, at or below it nothing happens. The third case `methC`
carries is a singular basis, and `pcaBasis_isUnit_det` is what rules it out here. No eigenvalue,
covariance or ordering of the axes appears — the point `reduceBy_outer` makes about a metric,
made once more about a spectral decomposition. `reduceByBasis_outer` holds at every invertible
basis, so what the principal axes contribute is tightness and never soundness.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* `Z` lies in the reduced zonotope

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `pca` over-approximates, at whatever principal axes it finds. -/
theorem Zonotope.reducePCA_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reducePCA o).construct := by
  unfold Zonotope.reducePCA
  split_ifs with hlt
  · exact Zonotope.reduceByBasis_outer Z _ (Z.pcaBasis_isUnit_det _)
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Zonotope.Real.Operations.ReducePCA
import CORALean.ContSet.Zonotope.Real.Theorems.PCABasisIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter

/-!
# `pca` over-approximates

Two cases, as Girard's rule and Combastel's have and `methC` does not: above
the order the basis is the principal axes, at or below it nothing happens. The
third case `methC` carries is a singular basis, and `pcaBasis_isUnit_det` is
what rules it out here.

No eigenvalue, no covariance and no ordering of the axes appears — the same
point `reduceBy_outer` makes about a metric, made once more about a spectral
decomposition. `reduceByBasis_outer` holds at every invertible basis, so what
the principal axes contribute is tightness and never soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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

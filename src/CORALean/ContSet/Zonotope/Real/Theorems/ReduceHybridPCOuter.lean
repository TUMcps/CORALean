import CORALean.ContSet.Zonotope.Real.Operations.ReduceHybridPC
import CORALean.ContSet.Zonotope.Real.Theorems.LineClBasisIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.PCABasisIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter

/-!
# `hybridPC` over-approximates

HybridPC [1, Sec. III-C] returns one of two reductions, each boxed along an
invertible basis: `lineClBasis_isUnit_det` and `pcaBasis_isUnit_det`. Whichever
the volume picks, `reduceByBasis_outer` applies.

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- HybridPC over-approximates, whichever of the two it keeps. -/
theorem Zonotope.reduceHybridPC_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) (ξ : ℝ)
    (fuel runs : ℕ) :
    Z.construct ⊆ (Z.reduceHybridPC o ξ fuel runs).construct := by -- --- PROOF ---
  unfold Zonotope.reduceHybridPC
  dsimp only
  split_ifs with hlt hv
  · exact Zonotope.reduceByBasis_outer Z _ (Z.lineClBasis_isUnit_det _ ξ fuel runs)
  · exact Zonotope.reduceByBasis_outer Z _ (Z.pcaBasis_isUnit_det _)
  · exact subset_rfl


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Zonotope.Real.Operations.ReduceMethC
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter

/-!
# `methC` over-approximates

Three cases now rather than Girard's and Combastel's two, because `methC`
chooses a basis as well as a partition: the basis where its determinant is a
unit, the axes where it is not, nothing below the order.

Neither the length filter nor the volume search appears — the same point
`reduceByOuter` makes about a metric, made once more about a combinatorial
search. That is what lets an exhaustive search be formalized here at all: it
has to return a basis, not a good one.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `methC` over-approximates, at whatever basis its search returns. -/
theorem Zonotope.reduceMethC_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceMethC o).construct := by -- --- PROOF ---
  unfold Zonotope.reduceMethC
  simp only []
  split_ifs with hlt hdet
  · exact Zonotope.reduceByBasis_outer Z _ hdet
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

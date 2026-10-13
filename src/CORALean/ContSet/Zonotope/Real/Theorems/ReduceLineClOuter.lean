module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceLineCl
public import CORALean.ContSet.Zonotope.Real.Theorems.LineClBasisIsUnitDet
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter

@[expose] public section

/-!
# `lineCl` over-approximates

[1, Alg. 3] encloses `Z` by `L_min · IH(L_min⁻¹ Z)`, and so does `reduceByBasis` at
any invertible matrix: `reduceByBasis_outer` is the whole argument, and
`lineClBasis_isUnit_det` is its hypothesis. Which clustering the runs find is a
matter of tightness and never of soundness, so nothing about distances, eigenvectors
or volumes enters.

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Line clustering over-approximates, at whatever basis the runs settle on. -/
theorem Zonotope.reduceLineCl_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) (ξ : ℝ) (fuel runs : ℕ) :
    Z.construct ⊆ (Z.reduceLineCl o ξ fuel runs).construct := by
  unfold Zonotope.reduceLineCl
  split_ifs with hlt
  · exact Zonotope.reduceByBasis_outer Z _ (Z.lineClBasis_isUnit_det _ ξ fuel runs)
  · exact subset_rfl


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

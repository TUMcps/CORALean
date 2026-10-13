module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceCoOptDir
public import CORALean.ContSet.Zonotope.Real.Theorems.PCABasisIsUnitDet
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfMulEqOneOfSumAbsLe

@[expose] public section

/-!
# CoOpt_dir over-approximates, whatever the solver returns

[1, Alg. 4]'s claim that the reduced zonotope encloses `Z`, for CoOpt_dir: a candidate kept is
invertible and meets eq. 10, so `C C⁻¹ = 1` and `subset_of_mul_eq_one_of_sum_abs_le` applies;
a candidate rejected leaves PCA's parallelotope, `reduceByBasis_outer` at the orthonormal
`U₀`. The solver is arbitrary: soundness does not rest on it converging, nor on it respecting
the constraint. Nothing is claimed about the volume, which is the solver's to minimize.

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

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 4], CoOpt_dir: `Z ⊆ reduceCoOptDir Z opt` for every solver `opt`. -/
theorem Zonotope.reduceCoOptDir_outer (Z : Zonotope (Vec ℝ n)) (opt : Mat ℝ n n → Mat ℝ n n) :
    Z.construct ⊆ (Z.reduceCoOptDir opt).construct := by -- --- PROOF ---
  unfold Zonotope.reduceCoOptDir
  dsimp only
  split_ifs with h
  · exact Z.subset_of_mul_eq_one_of_sum_abs_le (Matrix.mul_nonsing_inv _ h.1) h.2
  · exact Z.reduceByBasis_outer _ (Z.pcaBasis_isUnit_det _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

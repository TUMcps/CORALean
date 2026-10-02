import CORALean.ContSet.Zonotope.Real.Operations.ReduceCoOptSVD
import CORALean.ContSet.Zonotope.Real.Theorems.PCABasisIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfMulEqOneOfSumAbsLe

/-!
# CoOptSVD over-approximates, whatever the solver returns

[1, Alg. 4]: `Z ⊆ (c | U S Vᵀ)` whenever the candidate meets eq. 13. Eq. 12's inverse is a
right inverse there: `UᵀU = 1` makes `UUᵀ = 1` (square matrices), `VᵀV = 1` cancels the middle,
and `sᵢᵢ ≠ 0` makes `diag(s) diag(1/s) = 1`, so `C · V diag(1/s) Uᵀ = 1` and
`subset_of_mul_eq_one_of_sum_abs_le` applies. A rejected candidate leaves PCA's parallelotope.
Eq. 13 as printed omits `sᵢᵢ ≠ 0`, which its `1/sᵢᵢ` presumes. Nothing is claimed about the
volume.

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 4], CoOptSVD: `Z ⊆ reduceCoOptSVD Z opt` for every solver `opt`. -/
theorem Zonotope.reduceCoOptSVD_outer (Z : Zonotope (Vec ℝ n))
    (opt : Mat ℝ n n × Vec ℝ n × Mat ℝ n n → Mat ℝ n n × Vec ℝ n × Mat ℝ n n) :
    Z.construct ⊆ (Z.reduceCoOptSVD opt).construct := by -- --- PROOF ---
  unfold Zonotope.reduceCoOptSVD
  dsimp only
  split_ifs with h
  · obtain ⟨hU, hV, hS, hsum⟩ := h
    set U := (opt _).1
    set S := (opt _).2.1
    set V := (opt _).2.2
    refine Z.subset_of_mul_eq_one_of_sum_abs_le ?_ hsum
    -- `U S Vᵀ · V S⁻¹ Uᵀ = U (S S⁻¹) Uᵀ = U Uᵀ = 1`
    have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
    have hSS : Matrix.diagonal S * Matrix.diagonal S⁻¹ = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact mul_inv_cancel₀ (hS i)
    calc U * Matrix.diagonal S * Vᵀ * (V * Matrix.diagonal S⁻¹ * Uᵀ)
        = U * Matrix.diagonal S * (Vᵀ * V) * Matrix.diagonal S⁻¹ * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal S * Matrix.diagonal S⁻¹) * Uᵀ := by
          rw [hV, Matrix.mul_one, Matrix.mul_assoc U]
      _ = 1 := by rw [hSS, Matrix.mul_one, hUU]
  · exact Z.reduceByBasis_outer _ (Z.pcaBasis_isUnit_det _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

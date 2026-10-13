import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import Mathlib.Data.Matrix.Basic

/-!
# The constraint of constrained-optimization reduction

[1, Alg. 4]'s constraint, eqs. 9-10 and 13: `Z = (c | G) ⊆ (c | C)` once
`Σⱼ |(C⁻¹ G)ᵢⱼ| ≤ 1` for every row `i`. A point `c + Gβ` has `C⁻¹ Gβ` in the unit box, row by
row, and `C` maps it back. `C⁻¹` is any right inverse `M` here, `C M = 1`: eq. 10 writes
`C⁻¹`, eq. 13 writes `V diag(1/sᵢᵢ) Uᵀ`, and the two cases differ only in which `M` they name.

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

/-- [1, Alg. 4], eqs. 10 and 13: `Σⱼ |(M gⱼ)ᵢ| ≤ 1` for a right inverse `M` of `C` puts
`Z` inside the parallelotope `(c | C)`. -/
theorem Zonotope.subset_of_mul_eq_one_of_sum_abs_le (Z : Zonotope (Vec ℝ n)) {C M : Mat ℝ n n}
    (hCM : C * M = 1) (h : ∀ i, ∑ j, |(M *ᵥ Z.G j) i| ≤ 1) :
    Z.construct
      ⊆ (⟨n, Z.c, fun k i => C i k⟩ : Zonotope (Vec ℝ n)).construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  -- the coefficients in `C`'s columns: `M` applied to the generator part
  refine ⟨fun k => (M *ᵥ ∑ j, β j • Z.G j) k, fun k => ?_, ?_⟩
  · rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (h k))
    rw [abs_mul, mul_comm]
    exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)
  · set y := M *ᵥ ∑ j, β j • Z.G j
    have hmv : C *ᵥ y = ∑ j, β j • Z.G j := by
      rw [Matrix.mulVec_mulVec, hCM, Matrix.one_mulVec]
    have hcol : ∑ k, y k • (fun i => C i k : Vec ℝ n) = C *ᵥ y := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    show Z.c + ∑ j, β j • Z.G j = Z.c + ∑ k, y k • (fun i => C i k : Vec ℝ n)
    rw [hcol, hmv]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

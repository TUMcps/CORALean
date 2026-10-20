module

public import CORALean.Global.Tensor
public import CORALean.Global.NormTwoSqEqDotProduct

@[expose] public section

/-!
# A matrix with orthonormal rows preserves the Euclidean norm of a vector it is transposed onto

`[1, App. B]`: for `M Mᵀ = I`, `‖Mᵀ y‖₂ = ‖y‖₂`, since `(Mᵀy)ᵀ(Mᵀy) = yᵀ M Mᵀ y`. It is what
puts a ball of `ℝⁿ` into the image of a ball of `ℝᵐ` under `M`.

## Inputs
* `M` – matrix with orthonormal rows
* `y` – vector

## Hypotheses
* `hM` – the rows are orthonormal

## Conclusion
* the transposed image has the vector's Euclidean norm

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open WithLp Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem norm_two_transpose_mulVec_eq (M : Mat ℝ n m) (hM : M * Mᵀ = 1) (y : Fin n → ℝ) :
    ‖toLp 2 (Mᵀ *ᵥ y)‖ = ‖toLp 2 y‖ := by -- --- PROOF ---
  have hadj : ∀ (u : Fin m → ℝ) (v : Fin n → ℝ), (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := fun u v => by
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]
  have h : (Mᵀ *ᵥ y) ⬝ᵥ (Mᵀ *ᵥ y) = y ⬝ᵥ y := by
    rw [← hadj, mulVec_mulVec, hM, one_mulVec]
  have hsq : ‖toLp 2 (Mᵀ *ᵥ y)‖ ^ 2 = ‖toLp 2 y‖ ^ 2 := by
    rw [norm_two_sq_eq_dotProduct, norm_two_sq_eq_dotProduct, h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

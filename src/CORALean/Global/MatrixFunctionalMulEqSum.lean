module

public import CORALean.Global.MatrixFunctionalEqSumSingle
public import CORALean.Global.Basic

@[expose] public section

/-!
# A linear functional of a product `H X`

After `X ↦ H X`, a functional `f` is `X ↦ Σ (Hᵀ Z)_{ij} X_{ij}` with `Z_{kj} = f(E_{kj})`.

## Inputs
* `f` – linear functional on matrices
* `H` – left factor
* `X` – right factor

## Hypotheses
* none

## Conclusion
* the functional of the product is an entrywise sum against the transposed left factor
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m l : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- After `X ↦ H X`, it is `X ↦ Σ (Hᵀ Z)_{ij} X_{ij}` with `Z_{kj} = f(E_{kj})`. -/
theorem functional_mul_eq_sum (f : Matrix (Fin n) (Fin m) ℝ →ₗ[ℝ] ℝ)
    (H : Matrix (Fin n) (Fin l) ℝ) (X : Matrix (Fin l) (Fin m) ℝ) :
    f (H * X) = ∑ i, ∑ j,
      (Hᵀ * Matrix.of fun k j => f (single k j (1 : ℝ))) i j * X i j := by -- --- PROOF ---
  -- both sides are `tr((H X)ᵀ Z) = tr(Xᵀ (Hᵀ Z))`
  rw [functional_eq_sum_single f]
  have h := trace_transpose_mul_eq_sum (H * X)
    (Matrix.of fun k j => f (single k j (1 : ℝ)))
  rw [transpose_mul, Matrix.mul_assoc, trace_transpose_mul_eq_sum] at h
  simp only [of_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

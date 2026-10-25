module

public import CORALean.Global.Tensor
public import CORALean.Global.NormTwoSqEqDotProduct

@[expose] public section

/-!
# A matrix with orthonormal rows does not increase the Euclidean norm

`[1, App. B]`: for `M Mᵀ = I`, `‖M β‖₂ ≤ ‖β‖₂`: `β` is `Mᵀ(Mβ)` plus an orthogonal part, and
`‖Mᵀ(Mβ)‖₂ = ‖Mβ‖₂`. It puts the image of a ball of `ℝᵐ` under `M` into a ball of `ℝⁿ`.

## Inputs
* `M` – matrix with orthonormal rows
* `β` – coefficient vector

## Hypotheses
* `hM` – the rows are orthonormal

## Conclusion
* the Euclidean norm does not increase

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC), 2024.
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

theorem norm_two_mulVec_le (M : Mat ℝ n m) (hM : M * Mᵀ = 1) (β : Fin m → ℝ) : -- --- CONCL ---
    ‖toLp 2 (M *ᵥ β)‖ ≤ ‖toLp 2 β‖ := by -- --- PROOF ---
  have hadj : ∀ (u : Fin m → ℝ) (v : Fin n → ℝ), (M *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Mᵀ *ᵥ v) := fun u v => by
    rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]
  -- `β = Mᵀ M β + (β - Mᵀ M β)` with orthogonal parts
  set w := M *ᵥ β
  set b' := Mᵀ *ᵥ w
  have h1 : b' ⬝ᵥ b' = w ⬝ᵥ w := by
    rw [← hadj, mulVec_mulVec, hM, one_mulVec]
  have e1 : β ⬝ᵥ b' = w ⬝ᵥ w := (hadj β w).symm
  have h3 : β ⬝ᵥ β = b' ⬝ᵥ b' + (β - b') ⬝ᵥ (β - b') := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm b' β, e1, h1]
    ring
  have hsq : ‖toLp 2 w‖ ^ 2 ≤ ‖toLp 2 β‖ ^ 2 := by
    rw [norm_two_sq_eq_dotProduct, norm_two_sq_eq_dotProduct, h3, h1]
    have : 0 ≤ (β - b') ⬝ᵥ (β - b') := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

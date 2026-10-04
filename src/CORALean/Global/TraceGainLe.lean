import CORALean.Global.TraceMulVecMulVecSelf
import CORALean.Global.VecMulVecMulVecSelf
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-!
# The gain that minimizes a weighted trace

For a Gram matrix `S = Σₖ sₖ sₖᵀ` and a weight `W` with `vᵀ W v ≥ 0`, the trace
`tr(W (Λ S Λᵀ - Λ Lᵀ - L Λᵀ))` is least at any `Λ*` with `Λ* S = L`, so at `Λ* = L S⁻¹` when `S`
is invertible. Completing the square: with `Δ = Λ - Λ*`, the bracket is the one at `Λ*` plus
`Δ S Δᵀ = Σₖ (Δ sₖ)(Δ sₖ)ᵀ`, whose trace against `W` is `Σₖ (Δ sₖ)ᵀ W (Δ sₖ) ≥ 0`. This is the
step behind the Kalman gains of the zonotopic observers, which the papers take by setting a
matrix derivative to zero; no derivative is needed, and `W` drops out of the minimizer.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p : ℕ} {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem trace_gain_le (W : Mat ℝ n n) (hW : ∀ v, 0 ≤ v ⬝ᵥ (W *ᵥ v)) (s : ι → Vec ℝ p)
    (L Λs Λ : Mat ℝ n p) (hΛs : Λs * ∑ k, vecMulVec (s k) (s k) = L) :
    trace (W * (Λs * (∑ k, vecMulVec (s k) (s k)) * Λsᵀ - Λs * Lᵀ - L * Λsᵀ)) ≤
      trace (W * (Λ * (∑ k, vecMulVec (s k) (s k)) * Λᵀ - Λ * Lᵀ - L * Λᵀ)) := by -- --- PROOF ---
  set S : Mat ℝ p p := ∑ k, vecMulVec (s k) (s k) with hSdef
  have hST : Sᵀ = S := by simp [hSdef, transpose_sum, transpose_vecMulVec]
  set Δ := Λ - Λs
  have hΛ : Λ = Λs + Δ := by simp [Δ]
  have h1 : Λs * S * Δᵀ = L * Δᵀ := by rw [hΛs]
  have h2 : Δ * S * Λsᵀ = Δ * Lᵀ := by
    rw [Matrix.mul_assoc, ← hΛs, transpose_mul, hST]
  -- the bracket at `Λ` is the one at `Λ*` plus `Δ S Δᵀ`
  have hsq : Λ * S * Λᵀ - Λ * Lᵀ - L * Λᵀ =
      (Λs * S * Λsᵀ - Λs * Lᵀ - L * Λsᵀ) + Δ * S * Δᵀ := by
    calc Λ * S * Λᵀ - Λ * Lᵀ - L * Λᵀ
        = Λs * S * Λsᵀ + Λs * S * Δᵀ + Δ * S * Λsᵀ + Δ * S * Δᵀ - Λs * Lᵀ - Δ * Lᵀ -
            L * Λsᵀ - L * Δᵀ := by
          rw [hΛ]; simp only [transpose_add, Matrix.add_mul, Matrix.mul_add]; abel
      _ = _ := by rw [h1, h2]; abel
  -- and `Δ S Δᵀ` weighs in nonnegatively
  have hΔ : Δ * S * Δᵀ = ∑ k, vecMulVec (Δ *ᵥ s k) (Δ *ᵥ s k) := by
    simp only [hSdef, Matrix.mul_sum, Matrix.sum_mul, vecMulVec_mulVec_self]
  rw [hsq, Matrix.mul_add, trace_add, hΔ]
  refine le_add_of_nonneg_right ?_
  rw [Matrix.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [trace_mul_vecMulVec_self]
  exact hW _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeIntegralDeltaExpWeight

@[expose] public section

/-!
# The a posteriori error bound of Wang and Ye for the Arnoldi approximation of `e^{-τA}v`

[1, Thm. 3.1]: `‖e^{-τA}v - V_ke^{-τH_k}e₁‖₂ ≤ h_{k+1,k}e^{-min{ν(A),0}τ}∫₀^τ|h(t)|dt`,
`h(t) = e_k*e^{-tH_k}e₁` (3.7), `ν(A) = min Re W(A)` (3.4). It follows from the weighted bound
`Krylov.error_le_integral_delta_exp_weight`, whose weight `e^{(t-τ)ν}` is at most
`e^{-min{ν,0}τ}` on `[0, τ]`: `(t - τ)ν ≤ 0` for `ν ≥ 0`, and `(t - τ)ν ≤ -ντ` for `ν < 0`.
Stated for any real `ν` with `Re(x*Ax) ≥ ν x*x`, `ν(A)` included, and for the Krylov identity
(3.1) alone; `h_{k+1,k} ≥ 0`, `‖v_{k+1}‖₂ = 1` and `V_k` orthonormal enter only through the
factor `|h_{k+1,k}|‖v_{k+1}‖₂`.

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `w` – next vector
* `ν` – lower bound on the field of values
* `t` – time

## Hypotheses
* `hK` – Krylov identity holds
* `hA` – real part of the Rayleigh quotient at least the lower bound
* `ht` – time nonnegative

## Conclusion
* the Arnoldi error is at most the a posteriori integral estimate

## References

* [1] [H. Wang and Q. Ye. "Error bounds for the Krylov subspace methods for computations of matrix
      exponentials". SIAM Journal on Matrix Analysis and Applications,
      2017.](../../../../../../references/2017/wang-simax-krylov-error-bounds.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3.1]: under (3.1), `ν x*x ≤ Re(x*Ax)` and `v = V_ke₁`, `‖e^{-τA}v -
V_ke^{-τH_k}e₁‖₂ ≤ |h_{k+1,k}|‖v_{k+1}‖₂ e^{-min{ν,0}τ} ∫₀^τ|h(t)|dt` for `τ ≥ 0`; `V_k` has
`m + 1` columns. -/
theorem Krylov.error_le_exp_min_integral_delta (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (ν : ℝ)
    (hA : ∀ x : Fin n → ℂ, ν * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (A *ᵥ x)).re) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let h : ℝ → ℂ := fun s => exp (s • (-T)) (Fin.last m) 0
    ‖(WithLp.toLp 2 (exp (t • (-A)) *ᵥ v - V *ᵥ (exp (t • (-T)) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ *
        (Real.exp (-(min ν 0) * t) * ∫ s in (0 : ℝ)..t, ‖h s‖) := by -- --- PROOF ---
  intro v h
  have hmain := Krylov.error_le_integral_delta_exp_weight A V T τ w hK ν hA ht
  have hhc : Continuous h :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _)
  have hwc : Continuous fun s => ‖h s‖ * Real.exp ((s - t) * ν) :=
    hhc.norm.mul (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul
      continuous_const))
  have hint : ∫ s in (0 : ℝ)..t, ‖h s‖ * Real.exp ((s - t) * ν) ≤
      Real.exp (-(min ν 0) * t) * ∫ s in (0 : ℝ)..t, ‖h s‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ht (hwc.intervalIntegrable _ _)
      (((continuous_const (y := Real.exp (-(min ν 0) * t))).mul hhc.norm).intervalIntegrable _ _)
      fun s hs => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    rcases le_total ν 0 with hν | hν
    · rw [min_eq_left hν]; nlinarith [hs.1, hs.2]
    · rw [min_eq_right hν]; nlinarith [hs.1, hs.2]
  exact hmain.trans (mul_le_mul_of_nonneg_left hint (by positivity))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

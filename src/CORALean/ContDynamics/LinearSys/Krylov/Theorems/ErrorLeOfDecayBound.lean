module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeIntegralDeltaExpWeight

@[expose] public section

/-!
# From an exponential decay bound on `h` to the Arnoldi error bound, `t e^{-tz}`

The last step of [1, Thm. 5.2]: from `|h(s)| ≤ Ce^{-sz}` (5.2), where `z = z̃ ≤ a = ν(A)`
(5.5), to `‖e^{-τA}v - V_ke^{-τH_k}e₁‖₂ ≤ h_{k+1,k}Cτe^{-τz}`. The printed route integrates (5.2)
against the bound (3.6), `e^{-min{a,0}τ}∫₀^τ Ce^{-sz}ds`, and bounds `(e^x - 1)/x` by `1`, which
fails for `x = τz > 0` (`Krylov.wang_ye_integral_step_counterexample`). Integrating against the
weighted bound of the proof of Thm. 3.1 (`Krylov.error_le_integral_delta_exp_weight`) instead,
`e^{(s-τ)ν}Ce^{-sz} ≤ Ce^{-τz}` on `[0, τ]` as `z ≤ ν`, which gives the printed form.
Stated for any real `ν` with `Re(x*Ax) ≥ ν x*x` and the Krylov identity (3.1) alone.

## References

* [1] H. Wang, Q. Ye. "Error bounds for the Krylov subspace methods for computations of matrix
  exponentials". SIAM Journal on Matrix Analysis and Applications, 38(1):155-187, 2017.
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

/-- [1, Thm. 5.2]'s last step: under (3.1), `ν x*x ≤ Re(x*Ax)`, `v = V_ke₁`, `z ≤ ν` and
`|h(s)| ≤ Ce^{-sz}` on `[0, t]`, the error is at most `|h_{k+1,k}|‖v_{k+1}‖₂ C t e^{-tz}`. -/
theorem Krylov.error_le_of_decay_bound (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (ν : ℝ)
    (hA : ∀ x : Fin n → ℂ, ν * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (A *ᵥ x)).re) {t : ℝ}
    (ht : 0 ≤ t) (C z : ℝ) (hz : z ≤ ν)
    (hdec : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖exp (s • (-T)) (Fin.last m) 0‖ ≤ C * Real.exp (-(s * z))) :
    let v := V *ᵥ Pi.single 0 1
    ‖(WithLp.toLp 2 (exp (t • (-A)) *ᵥ v - V *ᵥ (exp (t • (-T)) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ *
        (C * t * Real.exp (-(t * z))) := by -- --- PROOF ---
  intro v
  have hmain := Krylov.error_le_integral_delta_exp_weight A V T τ w hK ν hA ht
  have hhc : Continuous fun s : ℝ => exp (s • (-T)) (Fin.last m) 0 :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _)
  have hwc : Continuous fun s : ℝ => ‖exp (s • (-T)) (Fin.last m) 0‖ * Real.exp ((s - t) * ν) :=
    hhc.norm.mul (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul
      continuous_const))
  -- the weighted integral of `|h|`, bounded by the integral of a constant
  have hint : ∫ s in (0 : ℝ)..t, ‖exp (s • (-T)) (Fin.last m) 0‖ * Real.exp ((s - t) * ν) ≤
      C * t * Real.exp (-(t * z)) := by
    -- pointwise `e^{(s-t)ν}Ce^{-sz} ≤ Ce^{-tz}`, as `(s - t)(ν - z) ≤ 0`
    have h1 : ∫ s in (0 : ℝ)..t, ‖exp (s • (-T)) (Fin.last m) 0‖ * Real.exp ((s - t) * ν) ≤
        ∫ _ in (0 : ℝ)..t, C * Real.exp (-(t * z)) := by
      refine intervalIntegral.integral_mono_on ht (hwc.intervalIntegrable _ _)
        intervalIntegrable_const fun s hs => ?_
      calc _ ≤ C * Real.exp (-(s * z)) * Real.exp ((s - t) * ν) :=
            mul_le_mul_of_nonneg_right (hdec s hs) (Real.exp_pos _).le
        _ = C * Real.exp (-(s * z) + (s - t) * ν) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ C * Real.exp (-(t * z)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
              (by simpa using (norm_nonneg _).trans (hdec 0 ⟨le_rfl, ht⟩))
            nlinarith [hs.1, hs.2]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    linarith
  exact hmain.trans (mul_le_mul_of_nonneg_left hint (by positivity))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

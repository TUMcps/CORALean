module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.IntegralOneSubPowMulPow
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-!
# The φ-functions: series and integral representation

[1, Eq. 4.1]: `φ_p(z) = Σ_k zᵏ/(k + p)!` (4.1a), `φ₀(z) = e^z`, and
`φ_p(z) = 1/(p - 1)! ∫₀¹(1 - θ)^{p-1}e^{θz}dθ` for `p ≥ 1` (4.1b). Stated for `z` in any complete
normed ℝ-algebra, so for complex `z` and for the matrices `σtA`, `σtT_m` of (4.2); `p ≥ 1` is
written `p + 1`. The exponential series of `e^{θz}`, integrated term by term against
`(1 - θ)ᵖ/p!` (dominated by the norms of the exponential series), gives the Beta integrals
`∫₀¹(1 - θ)ᵖθᵏdθ = k!p!/(k + p + 1)!`.

## Inputs
* `𝔸` – complete normed algebra
* `z` – element

## Hypotheses
* none

## Conclusion
* the φ-series equal the exponential and the Beta-type integral

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open NormedSpace


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 4.1]: `Σ_k zᵏ/k! = e^z`, and `Σ_k zᵏ/(k + p + 1)! = 1/p! ∫₀¹(1 - θ)ᵖe^{θz}dθ`, for
`z` in a complete normed ℝ-algebra. -/
theorem Krylov.phi_series_eq_integral {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (z : 𝔸) : -- --- CONCL ---
    ∑' k : ℕ, ((Nat.factorial (k + 0) : ℝ)⁻¹) • z ^ k = exp z ∧
      ∀ p : ℕ, ∑' k : ℕ, ((Nat.factorial (k + (p + 1)) : ℝ)⁻¹) • z ^ k =
        ((Nat.factorial p : ℝ)⁻¹) •
          ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p • exp (θ • z) := by -- --- PROOF ---
  have hexp : ∀ x : 𝔸, exp x = ∑' n : ℕ, ((Nat.factorial n : ℝ)⁻¹) • x ^ n := fun x =>
    congrFun (exp_eq_tsum ℝ) x
  refine ⟨by simp only [add_zero]; exact (hexp z).symm, fun p => ?_⟩
  -- the terms `(1 - θ)ᵖ θᵏ/k! zᵏ`, as continuous maps
  let F : ℕ → C(ℝ, 𝔸) := fun k =>
    ⟨fun θ => ((1 - θ) ^ p * ((Nat.factorial k : ℝ)⁻¹ * θ ^ k)) • z ^ k, by fun_prop⟩
  have hF : ∀ θ : ℝ, (1 - θ) ^ p • exp (θ • z) = ∑' k, F k θ := by
    intro θ
    rw [hexp, ← (expSeries_summable' (𝕂 := ℝ) (θ • z)).tsum_const_smul]
    refine tsum_congr fun k => ?_
    show _ = ((1 - θ) ^ p * ((Nat.factorial k : ℝ)⁻¹ * θ ^ k)) • z ^ k
    rw [smul_pow, smul_smul, smul_smul]
    ring_nf
  -- dominated on `[0, 1]` by the norms of the exponential series
  have hsum : Summable fun k : ℕ =>
      ‖(F k).restrict (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (norm_expSeries_summable' (𝕂 := ℝ) z)
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun θ => ?_
    obtain ⟨θ, hθ'⟩ := θ
    have hθ : θ ∈ Set.uIcc (0 : ℝ) 1 := hθ'
    rw [Set.uIcc_of_le zero_le_one] at hθ
    show ‖((1 - θ) ^ p * ((Nat.factorial k : ℝ)⁻¹ * θ ^ k)) • z ^ k‖ ≤ _
    -- `0 ≤ (1 - θ)ᵖ, θᵏ ≤ 1` on `[0, 1]`
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg (sub_nonneg.2 hθ.2) p), abs_of_nonneg (pow_nonneg hθ.1 k),
      abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    have h1 : (1 - θ) ^ p ≤ 1 := pow_le_one₀ (sub_nonneg.2 hθ.2) (by linarith [hθ.1])
    have h2 : θ ^ k ≤ 1 := pow_le_one₀ hθ.1 hθ.2
    have h3 : 0 ≤ (Nat.factorial k : ℝ)⁻¹ * ‖z ^ k‖ := by positivity
    calc (1 - θ) ^ p * ((Nat.factorial k : ℝ)⁻¹ * θ ^ k) * ‖z ^ k‖
        = (1 - θ) ^ p * θ ^ k * ((Nat.factorial k : ℝ)⁻¹ * ‖z ^ k‖) := by ring
      _ ≤ 1 * 1 * ((Nat.factorial k : ℝ)⁻¹ * ‖z ^ k‖) := by
        gcongr
        exact pow_nonneg hθ.1 k
      _ = _ := by ring
  -- each term integrates to `p!/(k + p + 1)! zᵏ`
  have hterm : ∀ k : ℕ, ((Nat.factorial p : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, F k θ =
      ((Nat.factorial (k + (p + 1)) : ℝ)⁻¹) • z ^ k := by
    intro k
    show _ • ∫ θ in (0 : ℝ)..1, ((1 - θ) ^ p * ((Nat.factorial k : ℝ)⁻¹ * θ ^ k)) • z ^ k = _
    rw [intervalIntegral.integral_smul_const, smul_smul]
    congr 1
    have h : ∀ θ : ℝ, (1 - θ) ^ p * ((Nat.factorial k : ℝ)⁻¹ * θ ^ k) =
        (Nat.factorial k : ℝ)⁻¹ * ((1 - θ) ^ p * θ ^ k) := fun θ => by ring
    simp only [h]
    rw [intervalIntegral.integral_const_mul, Krylov.integral_one_sub_pow_mul_pow,
      show k + p + 1 = k + (p + 1) by ring]
    field_simp
  have hS := (intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsum).const_smul
    ((Nat.factorial p : ℝ)⁻¹)
  simp only [hterm] at hS
  rw [hS.tsum_eq]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => (hF θ).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

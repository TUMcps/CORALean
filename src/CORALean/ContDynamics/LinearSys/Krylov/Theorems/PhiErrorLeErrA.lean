module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeErrA
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiErrorSubLeadingIsBigO

@[expose] public section

/-!
# Err_a for the Krylov approximation of φ-functions

[1, Thm. 2]: the error `L^p_m(t)v = φ_p(σtA)v - V_mφ_p(σtT_m)e₁` (4.3) of the Krylov
approximation (4.2) satisfies `L^p_m(t)v = τ_{m+1,m}γ_m(σt)^m/(m + p)! v_{m+1} + O(t^{m+1})`
(4.4a); in the nonexpansive case `‖L^p_m(t)v‖₂ ≤ τ_{m+1,m}γ_m t^m/(m + p)!` (4.4b), and the bound
is asymptotically correct. As in [1]: `p = 0` is `Prop. 1`, `Thm. 1` and `Prop. 3`; for `p ≥ 1`,
(4.1b) writes `L^p_m(t)v` as `1/(p-1)! ∫₀¹(1 - θ)^{p-1}L_m(θt)v dθ`, and `Prop. 1` (for (4.4a),
`Krylov.phi_error_sub_leading_isBigO`) and `Thm. 1` go under the integral, with the Beta integral
`∫₀¹(1 - θ)^{p-1}θᵐdθ = m!(p-1)!/(m+p)!`. `φ_p` is the series (4.1a); the asymptotic statements
hold for any `A`, the correctness of the bound as `t → 0⁺`.

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

open Matrix NormedSpace Asymptotics Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: (4.4a), (4.4b) under `W(σA) ⊆ ℂ⁻`, and (4.4b)'s asymptotic correctness, for
`φ_p` the series (4.1a), under (2.2) with `[V_m v_{m+1}]` orthonormal, `τ_{m+1,m} ≥ 0`,
upper Hessenberg `T_m`, `v = V_me₁`, `|σ| = 1`; `V_m` has `m + 1` columns here. -/
theorem Krylov.phi_error_le_errA (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℝ) (σ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + (τ : ℂ) • vecMulVec w (Pi.single (Fin.last m) 1))
    (hV : Vᴴ * V = 1) (hVw : Vᴴ *ᵥ w = 0) (hτ : 0 ≤ τ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ = 1)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0) (hσ : ‖σ‖ = 1)
    (p : ℕ) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    let L : ℝ → Fin n → ℂ := fun t =>
      (∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
        V *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • T)) ^ k) *ᵥ Pi.single 0 1)
    ((fun t : ℝ => L t - ((τ : ℂ) * γ * (σ * t) ^ (m + 1) /
        (Nat.factorial (m + 1 + p) : ℂ)) • w) =O[𝓝 0] fun t => t ^ (m + 2)) ∧
      ((∀ x : Fin n → ℂ, (star x ⬝ᵥ ((σ • A) *ᵥ x)).re ≤ 0) → ∀ t : ℝ, 0 ≤ t →
        ‖(WithLp.toLp 2 (L t) : EuclideanSpace ℂ (Fin n))‖ ≤
          τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℝ)) ∧
      ((fun t : ℝ => ‖(WithLp.toLp 2 (L t) : EuclideanSpace ℂ (Fin n))‖ -
        τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℝ))
          =O[𝓝[≥] 0] fun t => t ^ (m + 2)) := by -- --- PROOF ---
  intro v γ L
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  set E := (EuclideanSpace.equiv (Fin n) ℂ).symm with hE
  -- the exponential error `L_m(s)v` and its leading term
  set L0 : ℝ → Fin n → ℂ := fun s => exp (s • (σ • A)) *ᵥ v - V *ᵥ (exp (s • (σ • T)) *ᵥ e₁)
    with hL0
  have hL0c : Continuous L0 :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_mulVec
      continuous_const).sub (continuous_const.matrix_mulVec
        ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_mulVec
          continuous_const))
  -- `φ₀ = exp`, and for `p ≥ 1` the average (4.1b)
  have h0 : ∀ {k : ℕ} (M : Mat ℂ k k),
      (∑' j : ℕ, ((Nat.factorial j : ℝ)⁻¹) • M ^ j) = exp M := fun M => by
    have h := (Krylov.phi_series_eq_integral M).1
    simp only [add_zero] at h
    exact h
  have hrep : ∀ q : ℕ, p = q + 1 → ∀ t : ℝ,
      L t = ((Nat.factorial q : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ q • L0 (θ * t) := by
    rintro q rfl t
    exact Krylov.phi_error_eq_integral A V T σ v e₁ q t
  -- (4.4a)
  have ha := Krylov.phi_error_sub_leading_isBigO A V T (τ : ℂ) σ w hH hK p
  refine ⟨ha, fun hA t ht => ?_, ?_⟩
  · -- (4.4b)
    rcases p with _ | q
    · simpa only [L, h0, add_zero] using
        Krylov.error_le_errA A V T τ σ w hK hV hVw hτ hw hH hσ hA ht
    · have hfc : Continuous fun θ : ℝ => (1 - θ) ^ q • L0 (θ * t) :=
        (continuous_const.sub continuous_id).pow q |>.smul
          (hL0c.comp (continuous_id.mul continuous_const))
      -- `Thm. 1` at `θt`
      have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖E ((1 - θ) ^ q • L0 (θ * t))‖ ≤
          τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) * ((1 - θ) ^ q * θ ^ (m + 1)) := by
        intro θ hθ
        have h := Krylov.error_le_errA A V T τ σ w hK hV hVw hτ hw hH hσ hA
          (mul_nonneg hθ.1 ht)
        show ‖WithLp.toLp 2 ((1 - θ) ^ q • L0 (θ * t))‖ ≤ _
        rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.2 hθ.2) q)]
        refine (mul_le_mul_of_nonneg_left h (pow_nonneg (sub_nonneg.2 hθ.2) q)).trans
          (le_of_eq ?_)
        rw [mul_pow]
        ring
      -- the norm through the integral, then `Thm. 1` and the Beta integral
      rw [hrep q rfl t]
      calc ‖(WithLp.toLp 2 (((Nat.factorial q : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1,
            (1 - θ) ^ q • L0 (θ * t)) : EuclideanSpace ℂ (Fin n))‖
          = (Nat.factorial q : ℝ)⁻¹ * ‖∫ θ in (0 : ℝ)..1, E ((1 - θ) ^ q • L0 (θ * t))‖ := by
            rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
            congr 2
            exact ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).intervalIntegral_comp_comm
              (hfc.intervalIntegrable 0 1)).symm
        -- `‖∫f‖ ≤ ∫‖f‖`, then `Thm. 1` pointwise
        _ ≤ (Nat.factorial q : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..1, ‖E ((1 - θ) ^ q • L0 (θ * t))‖ :=
            mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm zero_le_one) (by positivity)
        _ ≤ (Nat.factorial q : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..1, τ * ‖γ‖ * t ^ (m + 1) /
              (Nat.factorial (m + 1) : ℝ) * ((1 - θ) ^ q * θ ^ (m + 1)) := by
            refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on zero_le_one
              ((E.continuous.comp hfc).norm.intervalIntegrable _ _)
              ((continuous_const.mul (((continuous_const.sub continuous_id).pow q).mul
                (continuous_pow _))).intervalIntegrable _ _) hpt)
              (by positivity)
        _ = τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1 + (q + 1)) : ℝ) := by
            rw [intervalIntegral.integral_const_mul, Krylov.integral_one_sub_pow_mul_pow,
              show m + 1 + q + 1 = m + 1 + (q + 1) by ring]
            field_simp
  · -- asymptotic correctness, from (4.4a) as in `Prop. 3`
    set b : ℝ → Fin n → ℂ := fun t =>
      ((τ : ℂ) * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℂ)) • w with hb
    have h1 := ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).isBigO_comp _ (𝓝 0)).trans ha
    have hb' : ∀ t : ℝ, 0 ≤ t →
        ‖E (b t)‖ = τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℝ) := by
      intro t ht
      show ‖WithLp.toLp 2 (b t)‖ = _
      rw [hb, WithLp.toLp_smul, norm_smul, hw, mul_one, norm_div, norm_mul, norm_mul, norm_pow,
        norm_mul, hσ, one_mul, Complex.norm_of_nonneg hτ, Complex.norm_real,
        Real.norm_of_nonneg ht, Complex.norm_natCast]
    -- `|‖a‖ - ‖b‖| ≤ ‖a - b‖`
    have h2 : (fun t : ℝ => ‖E (L t)‖ - τ * ‖γ‖ * t ^ (m + 1) /
        (Nat.factorial (m + 1 + p) : ℝ)) =O[𝓝[≥] 0] fun t => E (L t - b t) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hb' t ht, one_mul, Real.norm_eq_abs, map_sub]
      exact abs_norm_sub_norm_le _ _
    exact h2.trans (h1.mono nhdsWithin_le_nhds)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

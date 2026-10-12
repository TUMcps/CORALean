import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorSubLeadingIsBigO
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiErrorEqIntegral

/-!
# The leading term of the Krylov error of a φ-function

[1, Thm. 2]'s (4.4a): `L^p_m(t)v = φ_p(σtA)v - V_mφ_p(σtT_m)e₁ = τ_{m+1,m}γ_m(σt)^m/(m + p)!
v_{m+1} + O(t^{m+1})` as `t → 0`, for any `A`, under (2.2), upper Hessenberg `T_m` and
`v = V_me₁`, `φ_p` the series (4.1a). `p = 0` is `Prop. 1`; for `p ≥ 1`, (4.1b) averages
`L_m(θt)v` against `(1 - θ)^{p-1}/(p-1)!`, `Prop. 1`'s leading term integrates by the Beta
integral, and its remainder is bounded by `C|θt|^{m+1} ≤ C|t|^{m+1}` near `0`. [1] expands the
series (4.1a) instead. `τ_{m+1,m}` is any complex number here.

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Asymptotics Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]'s (4.4a): `φ_p(tσA)v - V_mφ_p(tσT_m)e₁ - τγ_m(σt)^m/(m + p)! v_{m+1} =
O(t^{m+1})`, under (2.2), upper Hessenberg `T_m`, `v = V_me₁`; `V_m` has `m + 1` columns. -/
theorem Krylov.phi_error_sub_leading_isBigO (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (p : ℕ) :
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    (fun t : ℝ => (∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
        V *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • T)) ^ k) *ᵥ
          Pi.single 0 1) - (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℂ)) • w)
      =O[𝓝 0] fun t => t ^ (m + 2) := by -- --- PROOF ---
  intro v γ
  set L : ℝ → Fin n → ℂ := fun t =>
    (∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
      V *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • T)) ^ k) *ᵥ Pi.single 0 1)
    with hLdef
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  -- the exponential error `L_m(s)v`
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
  show (fun t : ℝ => L t - (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℂ)) • w)
    =O[𝓝 0] fun t => t ^ (m + 2)
  have hP := Krylov.error_sub_leading_isBigO A V T τ σ w hH hK
  rcases p with _ | q
  · -- `p = 0`: `Prop. 1`
    refine hP.congr_left fun t => ?_
    simp only [L, h0, add_zero]
    rfl
  · -- `p ≥ 1`: `Prop. 1` under the integral, its remainder bounded near `0`
    obtain ⟨C, hCpos, hCw⟩ := hP.exists_pos
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hCw.bound
    set c0 : ℝ → ℂ := fun s =>
      τ * γ * (σ * s) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ) with hc0
    have hlead : ∀ t : ℝ, ((Nat.factorial q : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ q •
        (c0 (θ * t) • w) = (τ * γ * (σ * t) ^ (m + 1) /
          (Nat.factorial (m + 1 + (q + 1)) : ℂ)) • w := by
      intro t
      -- `(1 - θ)^q lead₀(θt) = (1 - θ)^qθ^{m+1} lead₀(t)`, then the Beta integral
      have hpt : ∀ θ : ℝ, (1 - θ) ^ q • (c0 (θ * t) • w) =
          ((1 - θ) ^ q * θ ^ (m + 1)) • (c0 t • w) := fun θ => by
        ext i
        simp only [hc0, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
        push_cast
        ring
      simp only [hpt]
      rw [intervalIntegral.integral_smul_const, Krylov.integral_one_sub_pow_mul_pow, smul_smul]
      ext i
      simp only [hc0, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
      rw [show m + 1 + q + 1 = m + 1 + (q + 1) by ring]
      have hq : (Nat.factorial q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
      have hm : (Nat.factorial (m + 1) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      push_cast
      field_simp
    -- `L - lead = 1/q! ∫₀¹(1 - θ)^q(L_m(θt)v - lead₀(θt))dθ`
    have hc0c : Continuous c0 := by simp only [hc0]; fun_prop
    refine IsBigO.of_bound ((Nat.factorial q : ℝ)⁻¹ * C) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    rw [Metric.mem_ball, dist_zero_right] at ht
    have hdiff : L t - (τ * γ * (σ * t) ^ (m + 1) /
        (Nat.factorial (m + 1 + (q + 1)) : ℂ)) • w = ((Nat.factorial q : ℝ)⁻¹) •
          ∫ θ in (0 : ℝ)..1, (1 - θ) ^ q • (L0 (θ * t) - c0 (θ * t) • w) := by
      rw [hrep q rfl t, ← hlead t, ← smul_sub, ← intervalIntegral.integral_sub]
      · simp only [smul_sub]
      · exact ((continuous_const.sub continuous_id).pow q |>.smul
          (hL0c.comp (continuous_id.mul continuous_const))).intervalIntegrable _ _
      · exact ((continuous_const.sub continuous_id).pow q |>.smul
          ((hc0c.comp (continuous_id.mul continuous_const)).smul
            continuous_const)).intervalIntegrable _ _
    -- and the remainder of `Prop. 1` is at most `C|θt|^{m+2} ≤ C|t|^{m+2}` under it
    rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- on `(0, 1]`, `|θt| ≤ |t| < ε`
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := C * ‖t ^ (m + 2)‖)
      (f := fun θ : ℝ => (1 - θ) ^ q • (L0 (θ * t) - c0 (θ * t) • w)) fun θ hθ => by
        rw [Set.uIoc_of_le zero_le_one] at hθ
        have hθt : dist (θ * t) 0 < ε := by
          rw [dist_zero_right, norm_mul, Real.norm_of_nonneg hθ.1.le]
          exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hθ.2) ht
        have hR : ‖L0 (θ * t) - c0 (θ * t) • w‖ ≤ C * ‖(θ * t) ^ (m + 2)‖ := hball hθt
        -- `(1 - θ)^q ≤ 1` and `|θt| ≤ |t|`
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.2 hθ.2) q)]
        have h1 : (1 - θ) ^ q ≤ 1 := pow_le_one₀ (sub_nonneg.2 hθ.2) (by linarith [hθ.1])
        have h2 : ‖(θ * t) ^ (m + 2)‖ ≤ ‖t ^ (m + 2)‖ := by
          rw [norm_pow, norm_pow, norm_mul, mul_pow]
          exact mul_le_of_le_one_left (by positivity)
            (pow_le_one₀ (norm_nonneg _) (by rw [Real.norm_of_nonneg hθ.1.le]; exact hθ.2))
        calc (1 - θ) ^ q * ‖L0 (θ * t) - c0 (θ * t) • w‖
            ≤ 1 * (C * ‖(θ * t) ^ (m + 2)‖) :=
              mul_le_mul h1 hR (norm_nonneg _) zero_le_one
          _ ≤ C * ‖t ^ (m + 2)‖ := by
              rw [one_mul]; exact mul_le_mul_of_nonneg_left h2 hCpos.le
    simpa using hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

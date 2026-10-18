module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.CorrectedKrylovIdentity
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpCorrectedApplyLastLe
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiErrorSubLeadingIsBigO

@[expose] public section

/-!
# The error bound for the corrected Krylov approximation of φ-functions

[1, Thm. 3]: the error `L^{p,+}_m(t)v = φ_p(σtA)v - V⁺_mφ_p(σtT⁺_m)e₁` (5.4) of the corrected
approximation, `T⁺_m = [T_m 0; τ_{m+1,m}e_m* 0]` (5.2a), `V⁺_m = [V_m v_{m+1}]` (5.3), satisfies
`L^{p,+}_m(t)v = τ_{m+1,m}γ_m(σt)^{m+1}/(m + p + 1)! Av_{m+1} + O(t^{m+2})` (5.9a), and in the
nonexpansive case `‖L^{p,+}_m(t)v‖₂ ≤ ‖Av_{m+1}‖₂τ_{m+1,m}γ_m t^{m+1}/(m + p + 1)!` (5.9b),
asymptotically correct. Not through `Prop. 5` (restated from Sidje's Expokit): `AV⁺_m = V⁺_mT⁺_m +
(Av_{m+1})e_{m+1}*` is a Krylov identity, so (5.9a) is (4.4a) for it, and (3.1b) for it with
`|e_{m+1}*e^{σsT⁺_m}e₁| ≤ τ_{m+1,m}γ_m s^m/m!` gives (5.9b) at `p = 0`, (4.1b) for `p ≥ 1`.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- (3.1b) for a Krylov identity with `τ = 1` and next vector `u`, given `|δ(r)| ≤ cr^{m+1}/
(m+1)!`: the exponential error is at most `‖u‖₂c s^{m+2}/(m+2)!`. -/
theorem Krylov.aux_corrected_exp_error_le (A : Mat ℂ n n) (Vp : Mat ℂ n (m + 2))
    (Tp : Mat ℂ (m + 2) (m + 2)) (σ : ℂ) (u : Fin n → ℂ) {c : ℝ}
    (hK : A * Vp = Vp * Tp + (1 : ℂ) • vecMulVec u (Pi.single (Fin.last (m + 1)) 1))
    (hA : ∀ x : Fin n → ℂ, (star x ⬝ᵥ ((σ • A) *ᵥ x)).re ≤ 0) (hσ : ‖σ‖ = 1)
    (hδ : ∀ r : ℝ, 0 ≤ r →
      ‖exp (r • (σ • Tp)) (Fin.last (m + 1)) 0‖ ≤ c * r ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
    {s : ℝ} (hs : 0 ≤ s) : -- --- STMT ---
    ‖(WithLp.toLp 2 (exp (s • (σ • A)) *ᵥ (Vp *ᵥ Pi.single 0 1) -
        Vp *ᵥ (exp (s • (σ • Tp)) *ᵥ Pi.single 0 1)) : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ * c * s ^ (m + 2) /
        (Nat.factorial (m + 2) : ℝ) := by -- --- PROOF ---
  have h31 := Krylov.error_le_integral_delta A Vp Tp 1 σ u hK hA hσ hs
  rw [norm_one, one_mul] at h31
  have hδc : Continuous fun r : ℝ => ‖exp (r • (σ • Tp)) (Fin.last (m + 1)) 0‖ :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _).norm
  have hint : ∫ r in (0 : ℝ)..s, ‖exp (r • (σ • Tp)) (Fin.last (m + 1)) 0‖ ≤
      ∫ r in (0 : ℝ)..s, c / (Nat.factorial (m + 1) : ℝ) * r ^ (m + 1) :=
    intervalIntegral.integral_mono_on hs (hδc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      ((continuous_const.mul (continuous_pow _)).intervalIntegrable (μ := MeasureTheory.volume)
        _ _) fun r hr => (hδ r hr.1).trans (le_of_eq (by ring))
  rw [intervalIntegral.integral_const_mul, integral_pow] at hint
  refine h31.trans ((mul_le_mul_of_nonneg_left hint (norm_nonneg _)).trans (le_of_eq ?_))
  rw [show m + 2 = m + 1 + 1 by ring, Nat.factorial_succ (m + 1)]
  push_cast
  field_simp
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]: (5.9a), (5.9b) under `W(σA) ⊆ ℂ⁻`, and (5.9b)'s asymptotic correctness, for
`φ_p` the series (4.1a), under (2.2) with `[V_m v_{m+1}]` orthonormal, `τ_{m+1,m} ≥ 0`, upper
Hessenberg `T_m`, `v = V_me₁`, `|σ| = 1`; `V_m` has `m + 1` columns here. -/
theorem Krylov.phi_corrected_error_le_errA (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℝ) (σ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + (τ : ℂ) • vecMulVec w (Pi.single (Fin.last m) 1))
    (hV : Vᴴ * V = 1) (hVw : Vᴴ *ᵥ w = 0) (hτ : 0 ≤ τ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0) (hσ : ‖σ‖ = 1) (p : ℕ) : -- --- STMT ---
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    let Tp : Mat ℂ (m + 2) (m + 2) := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 0 (fun j' => if j' = Fin.last m then (τ : ℂ) else 0) j)
        (fun i' => Fin.lastCases 0 (fun j' => T i' j') j) i
    let Vp : Mat ℂ n (m + 2) := Matrix.of fun i j => Fin.lastCases (w i) (fun j' => V i j') j
    let L : ℝ → Fin n → ℂ := fun t =>
      (∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
        Vp *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • Tp)) ^ k) *ᵥ
          Pi.single 0 1)
    -- (5.9a)
    ((fun t : ℝ => L t - ((τ : ℂ) * γ * (σ * t) ^ (m + 2) /
        (Nat.factorial (m + 1 + 1 + p) : ℂ)) • (A *ᵥ w)) =O[𝓝 0] fun t => t ^ (m + 3)) ∧
      -- (5.9b), and its asymptotic correctness
      ((∀ x : Fin n → ℂ, (star x ⬝ᵥ ((σ • A) *ᵥ x)).re ≤ 0) → ∀ t : ℝ, 0 ≤ t →
        ‖(WithLp.toLp 2 (L t) : EuclideanSpace ℂ (Fin n))‖ ≤
          ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℂ (Fin n))‖ * τ * ‖γ‖ * t ^ (m + 2) /
            (Nat.factorial (m + 1 + 1 + p) : ℝ)) ∧
      ((fun t : ℝ => ‖(WithLp.toLp 2 (L t) : EuclideanSpace ℂ (Fin n))‖ -
        ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℂ (Fin n))‖ * τ * ‖γ‖ * t ^ (m + 2) /
          (Nat.factorial (m + 1 + 1 + p) : ℝ)) =O[𝓝[≥] 0]
            fun t => t ^ (m + 3)) := by -- --- PROOF ---
  intro v γ Tp Vp L
  obtain ⟨hKp, hHp, hγp, hvp⟩ := Krylov.correctedKrylov_identity A V T (τ : ℂ) w hH hK
  set e₁ : Fin (m + 2) → ℂ := Pi.single 0 1 with he₁
  set E := (EuclideanSpace.equiv (Fin n) ℂ).symm with hE
  set c := ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℂ (Fin n))‖ with hc
  -- the exponential error of the corrected approximation
  set L0 : ℝ → Fin n → ℂ := fun s => exp (s • (σ • A)) *ᵥ v - Vp *ᵥ (exp (s • (σ • Tp)) *ᵥ e₁)
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
    exact Krylov.phi_error_eq_integral A Vp Tp σ v e₁ q t
  -- (5.9a): (4.4a) for the identity `AV⁺ = V⁺T⁺ + (Av_{m+1})e_{m+1}*`
  have ha : (fun t : ℝ => L t - ((τ : ℂ) * γ * (σ * t) ^ (m + 2) /
      (Nat.factorial (m + 1 + 1 + p) : ℂ)) • (A *ᵥ w)) =O[𝓝 0] fun t => t ^ (m + 3) := by
    have h := Krylov.phi_error_sub_leading_isBigO A Vp Tp 1 σ (A *ᵥ w) hHp hKp p
    dsimp only at h
    rw [hγp, hvp] at h
    refine h.congr_left fun t => ?_
    rw [show (1 : ℂ) * (γ * (τ : ℂ)) * (σ * t) ^ (m + 1 + 1) /
      (Nat.factorial (m + 1 + 1 + p) : ℂ) = (τ : ℂ) * γ * (σ * t) ^ (m + 2) /
        (Nat.factorial (m + 1 + 1 + p) : ℂ) by ring]
  refine ⟨ha, fun hA t ht => ?_, ?_⟩
  · -- (5.9b): `W(σT_m) ⊆ ℂ⁻` by (3.4), so `|e_{m+1}*e^{σsT⁺}e₁| ≤ τγ s^m/m!`
    have hGal : Vᴴ * A * V = T := by
      rw [Matrix.mul_assoc, hK, Matrix.mul_add, ← Matrix.mul_assoc, hV, Matrix.one_mul,
        Matrix.mul_smul, mul_vecMulVec, hVw, zero_vecMulVec, smul_zero, add_zero]
    -- `x*σT_mx = (V_mx)*σA(V_mx)`
    have hTW : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ ((σ • T) *ᵥ x)).re ≤ 0 := by
      intro x
      have h := hA (V *ᵥ x)
      rw [Matrix.smul_mulVec, dotProduct_smul] at h
      rw [← hGal, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
      exact h
    have hδp : ∀ r : ℝ, 0 ≤ r → ‖exp (r • (σ • Tp)) (Fin.last (m + 1)) 0‖ ≤
        τ * ‖γ‖ * r ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := fun r hr => by
      have h := Krylov.norm_exp_corrected_apply_last_le T (τ : ℂ) σ hH hTW hσ hr
      rwa [Complex.norm_real, Real.norm_of_nonneg hτ] at h
    -- (5.9b) at `p = 0`: (3.1b) for `AV⁺ = V⁺T⁺ + (Av_{m+1})e_{m+1}*`
    have hexp : ∀ s : ℝ, 0 ≤ s → ‖E (L0 s)‖ ≤
        c * (τ * ‖γ‖) * s ^ (m + 2) / (Nat.factorial (m + 2) : ℝ) := fun s hs => by
      have h := Krylov.aux_corrected_exp_error_le A Vp Tp σ (A *ᵥ w) hKp hA hσ hδp hs
      rw [hvp] at h
      exact h
    rcases p with _ | q
    · have h := hexp t ht
      simp only [L, h0, add_zero]
      exact h.trans (le_of_eq (by ring))
    · have hfc : Continuous fun θ : ℝ => (1 - θ) ^ q • L0 (θ * t) :=
        (continuous_const.sub continuous_id).pow q |>.smul
          (hL0c.comp (continuous_id.mul continuous_const))
      -- the exponential bound at `θt`
      have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖E ((1 - θ) ^ q • L0 (θ * t))‖ ≤
          c * (τ * ‖γ‖) * t ^ (m + 2) / (Nat.factorial (m + 2) : ℝ) *
            ((1 - θ) ^ q * θ ^ (m + 2)) := by
        intro θ hθ
        have h := hexp (θ * t) (mul_nonneg hθ.1 ht)
        show ‖WithLp.toLp 2 ((1 - θ) ^ q • L0 (θ * t))‖ ≤ _
        rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.2 hθ.2) q)]
        refine (mul_le_mul_of_nonneg_left h (pow_nonneg (sub_nonneg.2 hθ.2) q)).trans
          (le_of_eq ?_)
        rw [mul_pow]
        ring
      -- the norm through the integral, then the bound and the Beta integral
      rw [hrep q rfl t]
      calc ‖(WithLp.toLp 2 (((Nat.factorial q : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1,
            (1 - θ) ^ q • L0 (θ * t)) : EuclideanSpace ℂ (Fin n))‖
          = (Nat.factorial q : ℝ)⁻¹ * ‖∫ θ in (0 : ℝ)..1, E ((1 - θ) ^ q • L0 (θ * t))‖ := by
            rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
            congr 2
            exact ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).intervalIntegral_comp_comm
              (hfc.intervalIntegrable 0 1)).symm
        -- `‖∫f‖ ≤ ∫‖f‖`, then the bound pointwise
        _ ≤ (Nat.factorial q : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..1, ‖E ((1 - θ) ^ q • L0 (θ * t))‖ :=
            mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm zero_le_one) (by positivity)
        _ ≤ (Nat.factorial q : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..1, c * (τ * ‖γ‖) * t ^ (m + 2) /
              (Nat.factorial (m + 2) : ℝ) * ((1 - θ) ^ q * θ ^ (m + 2)) := by
            refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on zero_le_one
              ((E.continuous.comp hfc).norm.intervalIntegrable _ _)
              ((continuous_const.mul (((continuous_const.sub continuous_id).pow q).mul
                (continuous_pow _))).intervalIntegrable _ _) hpt)
              (by positivity)
        _ = c * τ * ‖γ‖ * t ^ (m + 2) / (Nat.factorial (m + 1 + 1 + (q + 1)) : ℝ) := by
            rw [intervalIntegral.integral_const_mul, Krylov.integral_one_sub_pow_mul_pow,
              show m + 2 + q + 1 = m + 1 + 1 + (q + 1) by ring]
            field_simp
  · -- asymptotic correctness, from (5.9a) as in `Prop. 3`
    set b : ℝ → Fin n → ℂ := fun t =>
      ((τ : ℂ) * γ * (σ * t) ^ (m + 2) / (Nat.factorial (m + 1 + 1 + p) : ℂ)) • (A *ᵥ w)
      with hb
    have h1 := ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).isBigO_comp _ (𝓝 0)).trans ha
    have hb' : ∀ t : ℝ, 0 ≤ t →
        ‖E (b t)‖ = c * τ * ‖γ‖ * t ^ (m + 2) / (Nat.factorial (m + 1 + 1 + p) : ℝ) := by
      intro t ht
      show ‖WithLp.toLp 2 (b t)‖ = _
      rw [hb, WithLp.toLp_smul, norm_smul, ← hc, norm_div, norm_mul, norm_mul, norm_pow,
        norm_mul, hσ, one_mul, Complex.norm_of_nonneg hτ, Complex.norm_real,
        Real.norm_of_nonneg ht, Complex.norm_natCast]
      ring
    -- `|‖a‖ - ‖b‖| ≤ ‖a - b‖`
    have h2 : (fun t : ℝ => ‖E (L t)‖ - c * τ * ‖γ‖ * t ^ (m + 2) /
        (Nat.factorial (m + 1 + 1 + p) : ℝ)) =O[𝓝[≥] 0] fun t => E (L t - b t) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hb' t ht, one_mul, Real.norm_eq_abs, map_sub]
      exact abs_norm_sub_norm_le _ _
    exact h2.trans (h1.mono nhdsWithin_le_nhds)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

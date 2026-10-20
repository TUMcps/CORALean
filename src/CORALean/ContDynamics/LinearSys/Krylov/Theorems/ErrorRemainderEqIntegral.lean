module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.DefectOfKrylovIdentity
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpEqSumAddPhiMul
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HessenbergPowApplyLastEqProd
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiErrorEqIntegral
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PowMulVecOfKrylovIdentity

@[expose] public section

/-!
# The remainder of the leading Krylov error term, explicitly

[1, Remark 2]: in (2.12), `R_{m+1}(t) = (σt)^{m+1}/m! ∫₀¹(A^{m+1}e^{σθtA}v -
V_mT_m^{m+1}e^{σθtT_m}e₁)(1 - θ)ᵐdθ`. `e^z = Σ_{j≤m} zʲ/j! + φ_{m+1}(z)z^{m+1}` splits the two
exponentials; the Taylor polynomials differ by the leading term of `Prop. 1` ((2.4), (2.5)), and
(4.1b) writes the two tails as one integral, `A^{m+1}` commuting with `e^{σθtA}`. Any `A`, under
(2.2), upper Hessenberg `T_m` and `v = V_me₁`.

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `σ` – time scale
* `w` – next vector
* `t` – time

## Hypotheses
* `hH` – Hessenberg matrix is upper Hessenberg
* `hK` – Krylov identity holds

## Conclusion
* the remainder of the leading error term equals the stated integral

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

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Remark 2]: `L_m(t)v - τ_{m+1,m}γ_m(σt)^m/m! v_{m+1} = (σt)^{m+1}/m! ∫₀¹(1 - θ)ᵐ
(A^{m+1}e^{θtσA}v - V_mT_m^{m+1}e^{θtσT_m}e₁)dθ`, under (2.2), upper Hessenberg `T_m` and
`v = V_me₁`; `V_m` has `m + 1` columns here. -/
theorem Krylov.error_remainder_eq_integral (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (t : ℝ) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    exp (t • (σ • A)) *ᵥ v - V *ᵥ (exp (t • (σ • T)) *ᵥ Pi.single 0 1) -
        (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w =
      ((σ * t) ^ (m + 2) / (Nat.factorial (m + 1) : ℂ)) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ (m + 1) •
        (A ^ (m + 2) *ᵥ (exp ((θ * t) • (σ • A)) *ᵥ v) -
          V *ᵥ (T ^ (m + 2) *ᵥ
            (exp ((θ * t) • (σ • T)) *ᵥ Pi.single 0 1))) := by -- --- PROOF ---
  intro v γ
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  -- `e^z = Σ_{j≤m+1} zʲ/j! + φ_{m+2}(z)z^{m+2}`, applied to a vector
  have hsplit : ∀ {k : ℕ} (M : Mat ℂ k k) (x : Fin k → ℂ), exp M *ᵥ x =
      ∑ j ∈ Finset.range (m + 1 + 1), ((Nat.factorial j : ℝ)⁻¹) • (M ^ j *ᵥ x) +
        (∑' i : ℕ, ((Nat.factorial (i + (m + 1 + 1)) : ℝ)⁻¹) • M ^ i) *ᵥ
          (M ^ (m + 1 + 1) *ᵥ x) := by
    intro k M x
    have h : exp M = ∑ j ∈ Finset.range (m + 1 + 1), ((Nat.factorial j : ℝ)⁻¹) • M ^ j +
        (∑' i : ℕ, ((Nat.factorial (i + (m + 1 + 1)) : ℝ)⁻¹) • M ^ i) * M ^ (m + 1 + 1) :=
      Krylov.exp_eq_sum_add_phi_mul M (m + 1 + 1)
    rw [h, Matrix.add_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Matrix.smul_mulVec]
  -- `(tσM)ʲx = (σt)ʲMʲx`
  have hpow : ∀ {k : ℕ} (M : Mat ℂ k k) (j : ℕ) (x : Fin k → ℂ),
      (t • (σ • M)) ^ j *ᵥ x = ((σ * t) ^ j) • (M ^ j *ᵥ x) := by
    intro k M j x
    rw [smul_pow, smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_pow, mul_comm]
    push_cast
    rfl
  -- the Taylor polynomials differ by the leading term, as in `Prop. 1`
  have hlow : ∀ j, j ≤ m → A ^ j *ᵥ v - V *ᵥ (T ^ j *ᵥ e₁) = 0 := fun j hjm => by
    rw [Krylov.pow_mulVec_of_krylovIdentity A V T τ w hH hK hjm, sub_self]
  have htop : A ^ (m + 1) *ᵥ v - V *ᵥ (T ^ (m + 1) *ᵥ e₁) = (τ * γ) • w := by
    have hd := Krylov.defect_of_krylovIdentity A V T τ 1 w hK (T ^ m *ᵥ e₁)
    rw [pow_succ', ← Matrix.mulVec_mulVec, Krylov.pow_mulVec_of_krylovIdentity A V T τ w hH hK
      le_rfl, pow_succ', ← Matrix.mulVec_mulVec, ← he₁]
    rw [one_smul, one_smul, one_mul] at hd
    rw [hd, he₁, Matrix.mulVec_single_one]
    show (τ * (T ^ m) (Fin.last m) 0) • w = _
    rw [Krylov.hessenberg_pow_apply_last_eq_prod T hH]
  -- the polynomial parts sum to the leading term
  have hpoly : ∑ j ∈ Finset.range (m + 1 + 1), ((Nat.factorial j : ℝ)⁻¹) •
      ((t • (σ • A)) ^ j *ᵥ v) - V *ᵥ ∑ j ∈ Finset.range (m + 1 + 1),
        ((Nat.factorial j : ℝ)⁻¹) • ((t • (σ • T)) ^ j *ᵥ e₁) =
      (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w := by
    rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ,
      Finset.sum_eq_zero fun j hj => by
        rw [Matrix.mulVec_smul, ← smul_sub, hpow, hpow, Matrix.mulVec_smul, ← smul_sub,
          hlow j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), smul_zero, smul_zero], zero_add,
      Matrix.mulVec_smul, ← smul_sub, hpow, hpow, Matrix.mulVec_smul, ← smul_sub, htop,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  -- the tails, `(σt)^{m+2}` factored out, are (4.1b)'s integral
  have htail := Krylov.phi_error_eq_integral A V T σ (A ^ (m + 1 + 1) *ᵥ v)
    (T ^ (m + 1 + 1) *ᵥ e₁) (m + 1) t
  rw [hsplit, hsplit, hpow A, hpow T, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul]
  -- `M^{m+2}` commutes with `e^{sσM}`
  have hcomm : ∀ {k : ℕ} (M : Mat ℂ k k) (s : ℝ) (x : Fin k → ℂ),
      exp (s • (σ • M)) *ᵥ (M ^ (m + 1 + 1) *ᵥ x) = M ^ (m + 1 + 1) *ᵥ (exp (s • (σ • M)) *ᵥ x) :=
    fun M s x => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ((((Commute.refl M).pow_left (m + 1 + 1)).smul_right σ).smul_right s).exp_right.eq]
  calc _ = (∑ j ∈ Finset.range (m + 1 + 1), ((Nat.factorial j : ℝ)⁻¹) • ((t • (σ • A)) ^ j *ᵥ v) -
        V *ᵥ ∑ j ∈ Finset.range (m + 1 + 1), ((Nat.factorial j : ℝ)⁻¹) • ((t • (σ • T)) ^ j *ᵥ e₁) -
          (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w) +
        ((σ * t) ^ (m + 1 + 1)) •
          ((∑' i : ℕ, ((Nat.factorial (i + (m + 1 + 1)) : ℝ)⁻¹) • (t • (σ • A)) ^ i) *ᵥ
            (A ^ (m + 1 + 1) *ᵥ v) - V *ᵥ ((∑' i : ℕ, ((Nat.factorial (i + (m + 1 + 1)) : ℝ)⁻¹) •
              (t • (σ • T)) ^ i) *ᵥ (T ^ (m + 1 + 1) *ᵥ e₁))) := by
        rw [smul_sub]
        abel
    -- the polynomial parts cancel, the tails are (4.1b)'s integral
    _ = _ := by
        rw [hpoly, sub_self, zero_add, htail, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
        congr 1
        · push_cast
          ring
        · refine intervalIntegral.integral_congr fun θ _ => ?_
          simp only [hcomm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

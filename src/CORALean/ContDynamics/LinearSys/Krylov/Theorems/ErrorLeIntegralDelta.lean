module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.DefectOfKrylovIdentity
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorEqIntegralDefect
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HasDerivAtExpSmulMulVec
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpSmulMulVecLe

@[expose] public section

/-!
# The Krylov error is bounded by the integral of `|δ_m|`, in the nonexpansive case

[1, Eq. 3.1b]: for `W(σA) ⊆ ℂ⁻`, `‖L_m(t)v‖₂ ≤ τ_{m+1,m}∫₀ᵗ|δ_m(s)|ds`,
`δ_m(s) = e_m*e^{σsT_m}e₁` (3.1a). The error solves `L' = σAL + D`, `L(0) = 0`, with the defect
`D_m(s)v = στ_{m+1,m}δ_m(s)v_{m+1}` (2.9), so (2.8) writes it as `∫₀ᵗE(t - s)D_m(s)v ds`, and
`‖E(t - s)‖₂ ≤ 1`, `|σ| = 1`. Only the Krylov identity (2.2) and `v = V_me₁` are used, not
`V_m*V_m = I`; `τ_{m+1,m}` is any complex number, entering as `|τ_{m+1,m}|`, and `v_{m+1}` any
vector, entering as the factor `‖v_{m+1}‖₂` that (2.2) makes `1`.

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

/-- [1, Eq. 3.1b]: under (2.2), `W(σA) ⊆ ℂ⁻`, `|σ| = 1` and `v = V_me₁`, `‖e^{tσA}v -
V_me^{tσT_m}e₁‖₂ ≤ |τ_{m+1,m}|‖v_{m+1}‖₂ ∫₀ᵗ|δ_m(s)|ds` for `t ≥ 0`; `V_m` has `m + 1`
columns. -/
theorem Krylov.error_le_integral_delta (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1))
    (hA : ∀ x : Fin n → ℂ, (star x ⬝ᵥ ((σ • A) *ᵥ x)).re ≤ 0) (hσ : ‖σ‖ = 1) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let δ : ℝ → ℂ := fun s => exp (s • (σ • T)) (Fin.last m) 0
    ‖(WithLp.toLp 2 (exp (t • (σ • A)) *ᵥ v - V *ᵥ (exp (t • (σ • T)) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ *
        ∫ s in (0 : ℝ)..t, ‖δ s‖ := by -- --- PROOF ---
  intro v δ
  set M := σ • A with hMdef
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  set y : ℝ → Fin n → ℂ := fun s => exp (s • M) *ᵥ v - V *ᵥ (exp (s • (σ • T)) *ᵥ e₁) with hydef
  set D : ℝ → Fin n → ℂ := fun s => (σ * τ * δ s) • w with hDdef
  have hδ : ∀ s, (exp (s • (σ • T)) *ᵥ e₁) (Fin.last m) = δ s := fun s => by
    rw [he₁, Matrix.mulVec_single_one]
    rfl
  -- `L' = σAL + D` with the defect (2.9)
  have hy : ∀ s, HasDerivAt y (M *ᵥ y s + D s) s := by
    intro s
    have h1 := Krylov.hasDerivAt_exp_smul_mulVec M v s
    let LV : (Fin (m + 1) → ℂ) →L[ℝ] (Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap ((Matrix.mulVecLin V).restrictScalars ℝ)
    have h2 : HasDerivAt (fun r : ℝ => V *ᵥ (exp (r • (σ • T)) *ᵥ e₁))
        (V *ᵥ ((σ • T) *ᵥ (exp (s • (σ • T)) *ᵥ e₁))) s :=
      LV.hasFDerivAt.comp_hasDerivAt s (Krylov.hasDerivAt_exp_smul_mulVec (σ • T) e₁ s)
    refine (h1.sub h2).congr_deriv ?_
    have hdef := Krylov.defect_of_krylovIdentity A V T τ σ w hK (exp (s • (σ • T)) *ᵥ e₁)
    rw [hδ] at hdef
    simp only [hydef, hDdef, hMdef, Matrix.mulVec_sub, ← hdef, Matrix.smul_mulVec,
      Matrix.mulVec_smul]
    abel
  have hy0 : y 0 = 0 := by
    show exp ((0 : ℝ) • M) *ᵥ (V *ᵥ e₁) - V *ᵥ (exp ((0 : ℝ) • (σ • T)) *ᵥ e₁) = 0
    simp only [zero_smul, exp_zero, Matrix.one_mulVec, sub_self]
  have hδc : Continuous δ :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _)
  have hDc : Continuous D := ((continuous_const.mul hδc).smul continuous_const)
  -- (2.8)
  have hrep := Krylov.error_eq_integral_defect M y D hy0 hy hDc t
  -- into Euclidean space, and the norm of the integral
  set E := (EuclideanSpace.equiv (Fin n) ℂ).symm with hE
  set f : ℝ → Fin n → ℂ := fun s => exp ((t - s) • M) *ᵥ D s with hf
  have hfc : Continuous f :=
    (exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)).matrix_mulVec
      hDc
  have hEf : Continuous fun s => E (f s) := E.continuous.comp hfc
  have hint : E (y t) = ∫ s in (0 : ℝ)..t, E (f s) := by
    rw [hrep]
    exact ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).intervalIntegral_comp_comm
      (hfc.intervalIntegrable _ _)).symm
  -- pointwise, `‖E(t-s)D(s)‖₂ ≤ ‖D(s)‖₂ = |τ||δ(s)|`
  set c := ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ with hc
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖E (f s)‖ ≤ c * ‖δ s‖ := by
    intro s hs
    have h := Krylov.norm_exp_smul_mulVec_le M hA (D s) (sub_nonneg.2 hs.2)
    refine h.trans (le_of_eq ?_)
    show ‖WithLp.toLp 2 ((σ * τ * δ s) • w)‖ = _
    rw [WithLp.toLp_smul, norm_smul, norm_mul, norm_mul, hσ, hc]
    ring
  calc ‖(WithLp.toLp 2 (y t) : EuclideanSpace ℂ (Fin n))‖ = ‖E (y t)‖ := rfl
    _ = ‖∫ s in (0 : ℝ)..t, E (f s)‖ := by rw [hint]
    _ ≤ ∫ s in (0 : ℝ)..t, ‖E (f s)‖ := intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ s in (0 : ℝ)..t, c * ‖δ s‖ :=
      intervalIntegral.integral_mono_on ht (hEf.norm.intervalIntegrable _ _)
        ((continuous_const.mul hδc.norm).intervalIntegrable _ _) hpt
    _ = c * ∫ s in (0 : ℝ)..t, ‖δ s‖ := intervalIntegral.integral_const_mul _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

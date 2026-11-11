module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorEqIntegralDefect
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HasDerivAtExpSmulMulVec
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpSmulMulVecLe

@[expose] public section

/-!
# The Krylov error with a residual in the Krylov identity, in the nonexpansive case

[1, Eq. 3.1b] for a Krylov identity that holds only up to a residual `Δ`:
`A V = V T + τ w e_m* + Δ`, with `‖Δ x‖₂ ≤ d‖x‖₂`. Then the error `y(s) = e^{sA}v - V e^{sT}e₁`
solves `y' = Ay + D`, `y(0) = 0`, with the defect `D(s) = τ δ(s) w + Δ e^{sT}e₁`, and for
`W(A), W(T) ⊆ ℂ⁻` both `e^{(t-s)A}` and `e^{sT}` are contractions. So the error is at most
`|τ|‖w‖∫₀ᵗ|δ(s)|ds + d t`. The residual is what the computed Arnoldi vectors and Hessenberg
matrix of floating point leave, orthogonal or not: neither `V*V = I` nor `V e₁ = v/‖v‖` enters.

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `w` – next vector
* `Δ` – residual of the Krylov identity
* `d` – bound on the residual's operator norm
* `t` – time

## Hypotheses
* `hK` – Krylov identity holds up to the residual
* `hΔ` – residual bounded
* `hA` – field of values of the matrix in the left half-plane
* `hT` – field of values of the Hessenberg matrix in the left half-plane
* `ht` – time nonnegative

## Conclusion
* the Krylov error is at most the integral of the defect bound plus the residual's share

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Under `A V = V T + τ w e_m* + Δ`, `‖Δ x‖₂ ≤ d‖x‖₂`, `W(A), W(T) ⊆ ℂ⁻` and `t ≥ 0`:
`‖e^{tA}Ve₁ - V e^{tT}e₁‖₂ ≤ |τ|‖w‖∫₀ᵗ|δ(s)|ds + d t`, `δ(s) = (e^{sT})_{m,1}`; `V` has
`m + 1` columns. -/
theorem Krylov.error_le_residual_integral (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℂ) (w : Fin n → ℂ) (Δ : Mat ℂ n (m + 1)) (d : ℝ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1) + Δ)
    (hΔ : ∀ x : Fin (m + 1) → ℂ,
      ‖(WithLp.toLp 2 (Δ *ᵥ x) : EuclideanSpace ℂ (Fin n))‖ ≤
        d * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖)
    (hA : ∀ x : Fin n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0)
    (hT : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ (T *ᵥ x)).re ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let δ : ℝ → ℂ := fun s => exp (s • T) (Fin.last m) 0
    ‖(WithLp.toLp 2 (exp (t • A) *ᵥ v - V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ * (∫ s in (0 : ℝ)..t, ‖δ s‖) +
        d * t := by -- --- PROOF ---
  intro v δ
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  set x : ℝ → Fin (m + 1) → ℂ := fun s => exp (s • T) *ᵥ e₁ with hxdef
  set y : ℝ → Fin n → ℂ := fun s => exp (s • A) *ᵥ v - V *ᵥ x s with hydef
  set D : ℝ → Fin n → ℂ := fun s => (τ * δ s) • w + Δ *ᵥ x s with hDdef
  have hδ : ∀ s, x s (Fin.last m) = δ s := fun s => by
    show (exp (s • T) *ᵥ e₁) (Fin.last m) = _
    rw [he₁, Matrix.mulVec_single_one]
    rfl
  -- `y' = Ay + D` with the defect `A V x - V T x = τ x_m w + Δ x`
  have hy : ∀ s, HasDerivAt y (A *ᵥ y s + D s) s := by
    intro s
    have h1 := Krylov.hasDerivAt_exp_smul_mulVec A v s
    let LV : (Fin (m + 1) → ℂ) →L[ℝ] (Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap ((Matrix.mulVecLin V).restrictScalars ℝ)
    have h2 : HasDerivAt (fun r : ℝ => V *ᵥ x r) (V *ᵥ (T *ᵥ x s)) s :=
      LV.hasFDerivAt.comp_hasDerivAt s (Krylov.hasDerivAt_exp_smul_mulVec T e₁ s)
    refine (h1.sub h2).congr_deriv ?_
    have hdef : A *ᵥ (V *ᵥ x s) - V *ᵥ (T *ᵥ x s) = (τ * δ s) • w + Δ *ᵥ x s := by
      rw [mulVec_mulVec, hK, add_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec,
        single_one_dotProduct, ← mulVec_mulVec, hδ, op_smul_eq_smul, smul_smul]
      abel
    simp only [hydef, hDdef, Matrix.mulVec_sub]
    rw [← hdef]
    abel
  -- the initial value and the continuity of the pieces
  have hy0 : y 0 = 0 := by
    show exp ((0 : ℝ) • A) *ᵥ (V *ᵥ e₁) - V *ᵥ (exp ((0 : ℝ) • T) *ᵥ e₁) = 0
    simp only [zero_smul, exp_zero, Matrix.one_mulVec, sub_self]
  have hxc : Continuous x :=
    (exp_continuous.comp (continuous_id.smul continuous_const)).matrix_mulVec continuous_const
  have hδc : Continuous δ :=
    (exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _
  have hDc : Continuous D :=
    ((hδc.const_mul τ).smul continuous_const).add (continuous_const.matrix_mulVec hxc)
  -- the integral representation of the error
  have hrep := Krylov.error_eq_integral_defect A y D hy0 hy hDc t
  set E := (EuclideanSpace.equiv (Fin n) ℂ).symm with hE
  set f : ℝ → Fin n → ℂ := fun s => exp ((t - s) • A) *ᵥ D s with hf
  have hfc : Continuous f :=
    (exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)).matrix_mulVec
      hDc
  have hEf : Continuous fun s => E (f s) := E.continuous.comp hfc
  have hint : E (y t) = ∫ s in (0 : ℝ)..t, E (f s) := by
    rw [hrep]
    exact ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).intervalIntegral_comp_comm
      (hfc.intervalIntegrable _ _)).symm
  -- the residual bound is nonnegative
  have hd : 0 ≤ d := by
    have h1 : ‖(WithLp.toLp 2 e₁ : EuclideanSpace ℂ (Fin (m + 1)))‖ = 1 :=
      (PiLp.norm_single 2 (fun _ => ℂ) 0 1).trans norm_one
    have := (norm_nonneg _).trans (hΔ e₁)
    rwa [h1, mul_one] at this
  -- pointwise, `‖E(t-s)D(s)‖₂ ≤ ‖D(s)‖₂ ≤ |τ||δ(s)|‖w‖₂ + d`, as `‖x(s)‖₂ ≤ ‖e₁‖₂ = 1`
  set c := ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ with hc
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖E (f s)‖ ≤ c * ‖δ s‖ + d := by
    intro s hs
    have h := Krylov.norm_exp_smul_mulVec_le A hA (D s) (sub_nonneg.2 hs.2)
    have hx : ‖(WithLp.toLp 2 (x s) : EuclideanSpace ℂ (Fin (m + 1)))‖ ≤ 1 := by
      have h1 := Krylov.norm_exp_smul_mulVec_le T hT e₁ hs.1
      have h2 : ‖(WithLp.toLp 2 e₁ : EuclideanSpace ℂ (Fin (m + 1)))‖ = 1 :=
        (PiLp.norm_single 2 (fun _ => ℂ) 0 1).trans norm_one
      exact h1.trans (le_of_eq h2)
    refine h.trans ?_
    show ‖(WithLp.toLp 2 ((τ * δ s) • w + Δ *ᵥ x s) : EuclideanSpace ℂ (Fin n))‖ ≤ _
    -- the defect splits into the Krylov share and the residual's
    rw [WithLp.toLp_add, WithLp.toLp_smul]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_smul, norm_mul, hc]
      ring
    · exact (hΔ (x s)).trans (mul_le_of_le_one_right hd hx)
  have hwc : Continuous fun s => c * ‖δ s‖ + d := (continuous_const.mul hδc.norm).add
    continuous_const
  -- the error is at most the integral of the pointwise bound
  calc ‖(WithLp.toLp 2 (y t) : EuclideanSpace ℂ (Fin n))‖ = ‖E (y t)‖ := rfl
    _ = ‖∫ s in (0 : ℝ)..t, E (f s)‖ := by rw [hint]
    _ ≤ ∫ s in (0 : ℝ)..t, ‖E (f s)‖ := intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ s in (0 : ℝ)..t, (c * ‖δ s‖ + d) :=
      intervalIntegral.integral_mono_on ht (hEf.norm.intervalIntegrable _ _)
        (hwc.intervalIntegrable _ _) hpt
    _ = c * (∫ s in (0 : ℝ)..t, ‖δ s‖) + d * t := by
      have h1 : IntervalIntegrable (fun s => c * ‖δ s‖) MeasureTheory.volume 0 t :=
        (continuous_const.mul hδc.norm).intervalIntegrable _ _
      rw [intervalIntegral.integral_add h1 intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
        sub_zero, mul_comm t d]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

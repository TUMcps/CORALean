module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.DefectOfKrylovIdentity
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorEqIntegralDefect
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HasDerivAtExpSmulMulVec
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpNegSmulMulVecLe

@[expose] public section

/-!
# The Arnoldi error for `e^{-τA}v` is bounded by a weighted integral of `|h|`

[1, Thm. 3.1], before its last step: `‖e^{-tA}v - V_ke^{-tH_k}e₁‖₂ ≤
h_{k+1,k}∫₀ᵗ|h(s)|e^{(s-t)ν(A)}ds`, `h(s) = e_k*e^{-sH_k}e₁` (3.7) and `ν(A) = min Re W(A)`.
The error solves `E' = -AE - h_{k+1,k}h(s)v_{k+1}`, `E(0) = 0` (Krylov identity (3.1)), so it is
`-h_{k+1,k}∫₀ᵗ h(s)e^{(s-t)A}v_{k+1}ds` (2.8 of Jawecki et al.), and `‖e^{(t-s)(-A)}‖ ≤
e^{(s-t)ν}` (`Krylov.norm_exp_neg_smul_mulVec_le`). Stated for any real `ν` with
`Re(x*Ax) ≥ ν x*x`, `ν(A)` included, and for any complex `h_{k+1,k}`, vector `v_{k+1}` and
`V_k`, `H_k` satisfying (3.1); neither orthonormality nor the Hessenberg form is used. CORA's
`priv_subspace_Krylov_individual_Wang` sums this integrand.

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
* the Arnoldi error is at most a weighted integral of the defect bound

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

/-- [1, Thm. 3.1]'s proof: under (3.1), `ν x*x ≤ Re(x*Ax)` and `v = V_ke₁`, `‖e^{-tA}v -
V_ke^{-tH_k}e₁‖₂ ≤ |h_{k+1,k}|‖v_{k+1}‖₂ ∫₀ᵗ|h(s)|e^{(s-t)ν}ds` for `t ≥ 0`; `V_k` has `m + 1`
columns. -/
theorem Krylov.error_le_integral_delta_exp_weight (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (ν : ℝ)
    (hA : ∀ x : Fin n → ℂ, ν * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (A *ᵥ x)).re) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let h : ℝ → ℂ := fun s => exp (s • (-T)) (Fin.last m) 0
    ‖(WithLp.toLp 2 (exp (t • (-A)) *ᵥ v - V *ᵥ (exp (t • (-T)) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ *
        ∫ s in (0 : ℝ)..t, ‖h s‖ * Real.exp ((s - t) * ν) := by -- --- PROOF ---
  intro v h
  set M : Mat ℂ n n := -A with hMdef
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  set y : ℝ → Fin n → ℂ := fun s => exp (s • M) *ᵥ v - V *ᵥ (exp (s • (-T)) *ᵥ e₁) with hydef
  set D : ℝ → Fin n → ℂ := fun s => (-τ * h s) • w with hDdef
  have hδ : ∀ s, (exp (s • (-T)) *ᵥ e₁) (Fin.last m) = h s := fun s => by
    rw [he₁, Matrix.mulVec_single_one]
    rfl
  -- `E' = -AE + D` with the defect
  have hy : ∀ s, HasDerivAt y (M *ᵥ y s + D s) s := by
    intro s
    have h1 := Krylov.hasDerivAt_exp_smul_mulVec M v s
    let LV : (Fin (m + 1) → ℂ) →L[ℝ] (Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap ((Matrix.mulVecLin V).restrictScalars ℝ)
    have h2 : HasDerivAt (fun r : ℝ => V *ᵥ (exp (r • (-T)) *ᵥ e₁))
        (V *ᵥ ((-T) *ᵥ (exp (s • (-T)) *ᵥ e₁))) s :=
      LV.hasFDerivAt.comp_hasDerivAt s (Krylov.hasDerivAt_exp_smul_mulVec (-T) e₁ s)
    refine (h1.sub h2).congr_deriv ?_
    have hdef := Krylov.defect_of_krylovIdentity A V T τ (-1) w hK (exp (s • (-T)) *ᵥ e₁)
    rw [hδ] at hdef
    simp only [hydef, hDdef, hMdef, Matrix.mulVec_sub, neg_one_smul, Matrix.neg_mulVec] at hdef ⊢
    rw [neg_one_mul, sub_neg_eq_add] at hdef
    rw [Matrix.mulVec_neg, ← hdef]
    abel
  -- `E(0) = v - V_ke₁ = 0`
  have hy0 : y 0 = 0 := by
    show exp ((0 : ℝ) • M) *ᵥ (V *ᵥ e₁) - V *ᵥ (exp ((0 : ℝ) • (-T)) *ᵥ e₁) = 0
    simp only [zero_smul, exp_zero, Matrix.one_mulVec, sub_self]
  -- `h` and the integrand are continuous
  have hhc : Continuous h :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _)
  have hDc : Continuous D := ((continuous_const.mul hhc).smul continuous_const)
  -- the integral representation
  have hrep := Krylov.error_eq_integral_defect M y D hy0 hy hDc t
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
  -- pointwise, `‖E(t-s)D(s)‖₂ ≤ e^{(s-t)ν}‖D(s)‖₂ = |τ||h(s)|e^{(s-t)ν}‖v_{k+1}‖₂`
  set c := ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ with hc
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖E (f s)‖ ≤ c * (‖h s‖ * Real.exp ((s - t) * ν)) := by
    intro s hs
    have hh := Krylov.norm_exp_neg_smul_mulVec_le A ν hA (D s) (r := t - s) (sub_nonneg.2 hs.2)
    refine hh.trans (le_of_eq ?_)
    show Real.exp (-((t - s) * ν)) * ‖WithLp.toLp 2 ((-τ * h s) • w)‖ = _
    rw [WithLp.toLp_smul, norm_smul, norm_mul, norm_neg, hc]
    have : -((t - s) * ν) = (s - t) * ν := by ring
    rw [this]
    ring
  have hwc : Continuous fun s => ‖h s‖ * Real.exp ((s - t) * ν) :=
    hhc.norm.mul (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul
      continuous_const))
  -- the norm of the integral is at most the integral of the bound
  calc ‖(WithLp.toLp 2 (y t) : EuclideanSpace ℂ (Fin n))‖ = ‖E (y t)‖ := rfl
    _ = ‖∫ s in (0 : ℝ)..t, E (f s)‖ := by rw [hint]
    _ ≤ ∫ s in (0 : ℝ)..t, ‖E (f s)‖ := intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ s in (0 : ℝ)..t, c * (‖h s‖ * Real.exp ((s - t) * ν)) :=
      intervalIntegral.integral_mono_on ht (hEf.norm.intervalIntegrable _ _)
        ((continuous_const.mul hwc).intervalIntegrable _ _) hpt
    _ = c * ∫ s in (0 : ℝ)..t, ‖h s‖ * Real.exp ((s - t) * ν) :=
      intervalIntegral.integral_const_mul _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

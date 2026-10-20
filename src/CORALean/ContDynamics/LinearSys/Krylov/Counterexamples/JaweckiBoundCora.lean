module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Arnoldi
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentPowMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# CORA's Krylov error test without the nonexpansive hypothesis

[1, Thm. 1] bounds the Krylov error by `τ_{m+1,m} γ_m t^m/m!` (Err_a) in the nonexpansive case
`W(σA) ⊆ ℂ⁻`, and only there. CORA's `priv_subspace_Krylov_individual_Jawecki` evaluates Err_a
for any matrix, and `priv_inputSolution_Krylov` and `priv_krylov_R_uTrans` use it on the
integrator matrix `C̃ = [A u; 0 0]` at `[0ₙ; 1]`, order `m ≥ 2`, then add a box of radius
`krylovError` to the Krylov approximation `V e^{tT}e₁`. At `A = [0 0; 1 1]`, `u = e₁`, Arnoldi
gives `V = [e₃ e₁]`, `τ₃,₂ = γ₂ = 1`, so Err_a is `t²/2`; `V` has no second coordinate, but
`(e^{tC̃}e₃)₂ = e^t - 1 - t > t²/2` for every `t > 0`. `A` is not nonexpansive: `e₂ᵀAe₂ = 1 > 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the Krylov error exceeds the Jawecki bound at every positive time

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

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]'s Err_a, as CORA evaluates it at order `m = 2` (`τ = h₃,₂`, `γ = h₂,₁`), on the
integrator matrix of `A = [0 0; 1 1]`, `u = e₁`: at every `t > 0` the error of the Krylov
approximation exceeds it in the second coordinate, and so in the 2-norm. -/
theorem Krylov.jawecki_bound_cora_counterexample : -- --- CONCL ---
    let A : Mat ℝ 2 2 := !![0, 0; 1, 1]
    let u : Vec ℝ 2 := ![1, 0]
    let C := Krylov.augment A u
    let v : Fin 3 → ℝ := Pi.single (Fin.last 2) 1
    let K := Krylov.arnoldi C v 2
    let V : Mat ℝ 3 2 := Matrix.of fun i j => K.1 j i
    let T : Mat ℝ 2 2 := Matrix.of fun i j => K.2 i j
    let τ : ℝ := K.2 2 1
    let γ : ℝ := K.2 1 0
    (∃ x : Vec ℝ 2, 0 < x ⬝ᵥ (A *ᵥ x)) ∧
      ∀ t : ℝ, 0 < t →
        let z := exp (t • C) *ᵥ v - ‖v‖₂ • (V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1))
        ‖v‖₂ * τ * γ * t ^ 2 / (Nat.factorial 2 : ℝ) < |z 1| ∧ |z 1| ≤ ‖z‖₂ := by -- --- PROOF ---
  intro A u C v K V T τ γ
  have hC : C = !![0, 0, 1; 1, 1, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hv : v = ![0, 0, 1] := by
    ext i
    fin_cases i <;> rfl
  have hnv : ‖v‖₂ = 1 := by
    rw [hv]
    simp [norm₂, Fin.sum_univ_three]
  -- Arnoldi: `v⁽¹⁾ = e₃`, `v⁽²⁾ = e₁`, `h₂,₁ = h₃,₂ = 1`
  have hK0 : K.1 0 = ![0, 0, 1] := by
    show ‖v‖₂⁻¹ • v = _
    rw [hnv, hv, inv_one, one_smul]
  have hK1 : K.1 1 = ![1, 0, 0] := by
    ext i
    fin_cases i <;>
      simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_three,
        dotProduct, vecHead, vecTail]
  have h10 : K.2 1 0 = 1 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_three,
      dotProduct, vecHead, vecTail]
  have h21 : K.2 2 1 = 1 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, hC, hv, norm₂, Fin.sum_univ_three,
      dotProduct, vecHead, vecTail]
  refine ⟨⟨![0, 1], ?_⟩, fun t ht => ?_⟩
  · simp [A, mulVec, dotProduct, Fin.sum_univ_two]
  intro z
  refine ⟨?_, abs_le_norm₂ z 1⟩
  -- the approximation has no second coordinate
  have hy : (V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1)) 1 = 0 := by
    simp [V, mulVec, dotProduct, Fin.sum_univ_two, hK0, hK1]
  -- the exact solution's second coordinate as a series
  set c : ℕ → ℝ := fun k => ((Nat.factorial k : ℝ))⁻¹ * t ^ k with hc
  have hS := (mulVecL.flip v).summable (Real.summable_exp_smul C t)
  have hL : exp (t • C) *ᵥ v = ∑' k : ℕ, c k • (C ^ k *ᵥ v) := by
    have h : (∑' k : ℕ, c k • C ^ k) *ᵥ v = ∑' k : ℕ, (c k • C ^ k) *ᵥ v :=
      ContinuousLinearMap.map_tsum (mulVecL.flip v) (Real.summable_exp_smul C t)
    rw [Real.exp_smul_tsum, h]
    exact tsum_congr fun k => Matrix.smul_mulVec _ _ _
  -- summable, and read off coordinate by coordinate
  have hS' : Summable fun k : ℕ => c k • (C ^ k *ᵥ v) := by
    have h : Summable fun k : ℕ => (c k • C ^ k) *ᵥ v := hS
    exact h.congr fun k => Matrix.smul_mulVec _ _ _
  have hcoord : (exp (t • C) *ᵥ v) 1 = ∑' k : ℕ, c k * (C ^ k *ᵥ v) 1 := by
    rw [hL]
    have h := ContinuousLinearMap.map_tsum
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) hS'
    simpa using h
  -- `(C̃ᵏ e₃)₂` is `0` for `k ≤ 1` and `1` from `k = 2` on
  have hpow : ∀ j : ℕ, (A ^ (j + 1) *ᵥ u) 1 = 1 := by
    intro j
    induction j with
    | zero => simp [A, u, mulVec, dotProduct, Fin.sum_univ_two]
    | succ j ih =>
      -- `Aʲ⁺¹e₁ = e₂` for all `j`: the first coordinate stays `0`
      have h0 : ∀ j : ℕ, (A ^ (j + 1) *ᵥ u) 0 = 0 := by
        intro j
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        simp [A, mulVec, dotProduct, Fin.sum_univ_two]
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have := h0 j
      simp only [mulVec, dotProduct, Fin.sum_univ_two] at this ih ⊢
      simp [A, this, ih]
  -- through `C̃ᵏ⁺¹e₃ = [Aᵏu; 0]`
  have hterm : ∀ k : ℕ, (C ^ (k + 2) *ᵥ v) 1 = 1 := by
    intro k
    have h := congrFun (Krylov.augment_pow_mulVec A u (k + 1)).1 1
    rw [hpow k] at h
    exact h
  -- so every term of the series is nonnegative
  have hnonneg : ∀ k : ℕ, 0 ≤ c k * (C ^ k *ᵥ v) 1 := by
    intro k
    rcases k with _ | _ | k
    · simp [hv]
    · simp [hC, hv, mulVec, dotProduct, Fin.sum_univ_three]
    · rw [hterm k, mul_one]
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (pow_nonneg ht.le _)
  have hsum : Summable fun k : ℕ => c k * (C ^ k *ᵥ v) 1 := by
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).summable hS'
    simpa using h
  -- the terms `k = 2, 3` alone exceed `t²/2`
  have hlow : t ^ 2 / 2 + t ^ 3 / 6 ≤ ∑' k : ℕ, c k * (C ^ k *ᵥ v) 1 := by
    have h := hsum.sum_le_tsum ({2, 3} : Finset ℕ) (fun k _ => hnonneg k)
    rw [Finset.sum_pair (by norm_num), hterm 0, hterm 1] at h
    simp only [hc, Nat.factorial] at h
    norm_num at h
    linarith
  have hz : z 1 = (exp (t • C) *ᵥ v) 1 := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, hy, smul_eq_mul, mul_zero, sub_zero]
  rw [hz, hcoord, hnv, show τ = 1 from h21, show γ = 1 from h10]
  have h3 : 0 < t ^ 3 / 6 := by positivity
  rw [abs_of_nonneg (by linarith [hlow, sq_nonneg t])]
  norm_num [Nat.factorial]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

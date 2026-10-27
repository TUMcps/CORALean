module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorSubLeadingIsBigO
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HessenbergPowApplyEqZero

@[expose] public section

/-!
# The leading term of the defect, and the orders of defect and error

[1, Eq. 2.10]: `D_m(t)v = στ_{m+1,m}γ_m(σt)^{m-1}/(m-1)! v_{m+1} + O(t^m)` as `t → 0`, from the
Taylor series of `e^{σtT_m}` with (2.3) and (2.5); hence `‖D_m(t)v‖ = O(t^{m-1})` and, with
(2.8), `‖L_m(t)v‖ = O(t^m)` (2.11). Here `D_m(t)v = στ_{m+1,m}δ_m(t)v_{m+1}` (2.9),
`δ_m(t) = (e^{σtT_m})_{m,1}` is expanded to order `m - 1`, and the order of `L_m(t)v` is read off
`Prop. 1`. No hypothesis on `A`; `O(·)` in the sup norm of `Fin n → ℂ`, the same in any norm.

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `σ` – time scale
* `w` – next vector

## Hypotheses
* `hH` – Hessenberg matrix is upper Hessenberg
* `hK` – Krylov identity holds

## Conclusion
* defect and error have the stated orders as time tends to zero

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
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

/-- [1, Eq. 2.10] and (2.11): under (2.2), upper Hessenberg `T_m` and `v = V_me₁`,
`D_m(t)v - στγ_m(σt)^{m-1}/(m-1)! v_{m+1} = O(t^m)`, `D_m(t)v = O(t^{m-1})` and
`L_m(t)v = O(t^m)` as `t → 0`; `V_m` has `m + 1` columns here. -/
theorem Krylov.defect_sub_leading_isBigO (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    let S : ℝ → Fin (m + 1) → ℂ := fun t => exp (t • (σ • T)) *ᵥ Pi.single 0 1
    let D : ℝ → Fin n → ℂ := fun t => σ • (A *ᵥ (V *ᵥ S t)) - σ • (V *ᵥ (T *ᵥ S t))
    ((fun t : ℝ => D t - (σ * τ * γ * (σ * t) ^ m / (Nat.factorial m : ℂ)) • w)
        =O[𝓝 0] fun t => t ^ (m + 1)) ∧
      ((fun t : ℝ => D t) =O[𝓝 0] fun t => t ^ m) ∧
      ((fun t : ℝ => exp (t • (σ • A)) *ᵥ v - V *ᵥ S t) =O[𝓝 0]
        fun t => t ^ (m + 1)) := by -- --- PROOF ---
  intro v γ S D
  -- `C(σt)ᵏu = O(tᵏ)`, and `t^{k+1} = O(tᵏ)` near `0`
  have hpow : ∀ (C : ℂ) (u : Fin n → ℂ) (k : ℕ),
      (fun t : ℝ => (C * (σ * t) ^ k) • u) =O[𝓝 0] fun t => t ^ k := by
    intro C u k
    refine IsBigO.of_bound (‖C‖ * ‖σ‖ ^ k * ‖u‖) (Eventually.of_forall fun t => ?_)
    rw [norm_smul, norm_mul, norm_pow, norm_mul, Complex.norm_real, norm_pow, mul_pow]
    exact le_of_eq (by ring)
  have hup : ∀ k : ℕ, (fun t : ℝ => t ^ (k + 1)) =O[𝓝 0] fun t => t ^ k := by
    intro k
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, dist_zero_right] at ht
    rw [norm_pow, norm_pow, one_mul, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) ht.le
  -- `δ_m(t) = γ(σt)^{m-1}/(m-1)! + O(t^m)`, by (2.3) and (2.5)
  have hcol : ∀ j, ((σ • T) ^ j *ᵥ Pi.single 0 1) (Fin.last m) = σ ^ j * (T ^ j) (Fin.last m) 0 :=
    fun j => by rw [smul_pow, Matrix.mulVec_single_one]; rfl
  have hδ : (fun t : ℝ => S t (Fin.last m) - γ * (σ * t) ^ m / (Nat.factorial m : ℂ))
      =O[𝓝 0] fun t => t ^ (m + 1) := by
    have h := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 1) => ℂ)
      (Fin.last m)).isBigO_comp _ (𝓝 0)).trans
      (Krylov.exp_smul_mulVec_taylor_isBigO (σ • T) (Pi.single 0 1) (m + 1))
    refine h.congr_left fun t => ?_
    simp only [ContinuousLinearMap.proj_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hcol]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => by
      rw [Krylov.hessenberg_pow_apply_eq_zero T hH j (Fin.last m) 0
        (by simp only [Fin.val_zero, Fin.val_last, zero_add]; exact Finset.mem_range.1 hj),
        mul_zero, mul_zero], zero_add, Krylov.hessenberg_pow_apply_last_eq_prod T hH]
    rw [mul_pow]
    field_simp
    rfl
  -- (2.9): `D_m(t)v = στδ_m(t)v_{m+1}`
  have hD : ∀ t, D t = (σ * τ * S t (Fin.last m)) • w := fun t =>
    Krylov.defect_of_krylovIdentity A V T τ σ w hK (S t)
  have h1 : (fun t : ℝ => D t - (σ * τ * γ * (σ * t) ^ m / (Nat.factorial m : ℂ)) • w)
      =O[𝓝 0] fun t => t ^ (m + 1) := by
    refine (((ContinuousLinearMap.toSpanSingleton ℂ ((σ * τ) • w)).isBigO_comp _ (𝓝 0)).trans
      hδ).congr_left fun t => ?_
    rw [hD t, ContinuousLinearMap.toSpanSingleton_apply, smul_smul, ← sub_smul]
    congr 1
    ring
  refine ⟨h1, ?_, ?_⟩
  · -- `D = (D - lead) + lead`
    refine ((h1.trans (hup m)).add (hpow (σ * τ * γ / (Nat.factorial m : ℂ)) w m)).congr_left
      fun t => ?_
    rw [show σ * τ * γ / (Nat.factorial m : ℂ) * (σ * t) ^ m =
      σ * τ * γ * (σ * t) ^ m / (Nat.factorial m : ℂ) by ring, sub_add_cancel]
  · -- `L = (L - lead) + lead`, by `Prop. 1`
    have hP := Krylov.error_sub_leading_isBigO A V T τ σ w hH hK
    refine ((hP.trans (hup (m + 1))).add
      (hpow (τ * γ / (Nat.factorial (m + 1) : ℂ)) w (m + 1))).congr_left fun t => ?_
    rw [show τ * γ / (Nat.factorial (m + 1) : ℂ) * (σ * t) ^ (m + 1) =
      τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ) by ring, sub_add_cancel]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

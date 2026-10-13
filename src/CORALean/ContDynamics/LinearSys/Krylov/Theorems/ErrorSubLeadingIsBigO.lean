module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.DefectOfKrylovIdentity
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpSmulMulVecTaylorIsBigO
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HessenbergPowApplyLastEqProd
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PowMulVecOfKrylovIdentity

@[expose] public section

/-!
# The leading term of the Krylov error, for any `A`

[1, Prop. 1]: `L_m(t)v = τ_{m+1,m}γ_m(σt)^m/m! v_{m+1} + R_{m+1}(t)`, `R_{m+1}(t) = O(t^{m+1})`
(2.12) as `t → 0`. As in [1]: the Taylor expansions of `e^{σtA}v` and `V_me^{σtT_m}e₁` to order
`m` agree below `m` by (2.4), and at `m`, `Aᵐv - V_mT_mᵐe₁ = τ_{m+1,m}(e_m*T_m^{m-1}e₁)v_{m+1}`
by (2.2), with `γ_m` from (2.5). No hypothesis on `A`; `O(·)` in the sup norm of `Fin n → ℂ`,
the same in any norm.

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

/-- [1, Prop. 1]: under (2.2), upper Hessenberg `T_m` and `v = V_me₁`,
`e^{tσA}v - V_me^{tσT_m}e₁ - τ_{m+1,m}γ_m(σt)^m/m! v_{m+1} = O(t^{m+1})` as `t → 0`; `V_m` has
`m + 1` columns here. -/
theorem Krylov.error_sub_leading_isBigO (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) :
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    (fun t : ℝ => exp (t • (σ • A)) *ᵥ v - V *ᵥ (exp (t • (σ • T)) *ᵥ Pi.single 0 1) -
        (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w)
      =O[𝓝 0] fun t => t ^ (m + 2) := by -- --- PROOF ---
  intro v γ
  set e₁ : Fin (m + 1) → ℂ := Pi.single 0 1 with he₁
  set c : ℝ → ℕ → ℂ := fun t j => (Nat.factorial j : ℂ)⁻¹ * (t : ℂ) ^ j with hc
  -- the two Taylor expansions to order `m + 1`, the second through `y ↦ V_my`
  have h1 := Krylov.exp_smul_mulVec_taylor_isBigO (σ • A) v (m + 2)
  have h2 := ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin V)).isBigO_comp _ (𝓝 0)).trans
    (Krylov.exp_smul_mulVec_taylor_isBigO (σ • T) e₁ (m + 2))
  -- below order `m + 1` the terms agree (2.4); at `m + 1` they differ by `τγ v_{m+1}`
  have hj : ∀ j, (σ • A) ^ j *ᵥ v - V *ᵥ ((σ • T) ^ j *ᵥ e₁) =
      σ ^ j • (A ^ j *ᵥ v - V *ᵥ (T ^ j *ᵥ e₁)) := fun j => by
    rw [smul_pow, smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_sub]
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
  -- the difference of the two Taylor polynomials is the leading term
  have hS : ∀ t : ℝ, ∑ j ∈ Finset.range (m + 2), c t j • ((σ • A) ^ j *ᵥ v) -
      V *ᵥ ∑ j ∈ Finset.range (m + 2), c t j • ((σ • T) ^ j *ᵥ e₁) =
      (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w := by
    intro t
    rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ,
      Finset.sum_eq_zero fun j hj' => by
        rw [Matrix.mulVec_smul, ← smul_sub, hj, hlow j (Nat.lt_succ_iff.1
          (Finset.mem_range.1 hj')), smul_zero, smul_zero], zero_add, Matrix.mulVec_smul,
      ← smul_sub, hj, htop, smul_smul, smul_smul]
    congr 1
    simp only [hc]
    rw [mul_pow]
    field_simp
  -- so the error minus the leading term is the difference of the two remainders
  refine (h1.sub h2).congr_left fun t => ?_
  show _ = _ - (τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w
  rw [← hS t]
  simp only [hc, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
    Matrix.mulVec_sub]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

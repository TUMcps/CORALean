module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.CorrectedKrylovIdentity
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HessenbergPowApplyEqZero
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiErrorSubLeadingIsBigO
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiSmulMulVecTaylorIsBigO

@[expose] public section

/-!
# The leading terms `τt e_m*φ_{p+1}(σtT_m)e₁` of the Krylov errors

[1, Remark 4]: `e_m*φ_j(σtT_m)e₁ = γ_m(σt)^{m-1}/(m - 1 + j)! + O(t^m)` (5.6), from (4.1a),
(2.3) and (2.5); the leading terms `L^p_m(t)v = τ_{m+1,m}σt(e_m*φ_{p+1}(σtT_m)e₁)v_{m+1} + O(t^m)`
(5.7a) and `L^{p,+}_m(t)v = τ_{m+1,m}(σt)²(e_m*φ_{p+2}(σtT_m)e₁)Av_{m+1} + O(t^{m+1})` (5.7b).
(5.6) is the Taylor expansion of `φ_j`; (5.7a) and (5.7b) are proved with the remainders
`O(t^{m+1})` and `O(t^{m+2})`, one order more than printed (each leading term is itself of the
printed order), from (4.4a), (5.9a) and (5.6), not from the restated series (5.5a), (5.5b).
Any `A`, under (2.2), upper Hessenberg `T_m`, `v = V_me₁`; `φ_p` the series (4.1a).

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

/-- [1, Remark 4]: (5.6), and (5.7a), (5.7b) with remainders `O(t^{m+1})`, `O(t^{m+2})`, under
(2.2), upper Hessenberg `T_m`, `v = V_me₁`, `T⁺_m` (5.2a), `V⁺_m` (5.3); `V_m` has `m + 1`
columns here. -/
theorem Krylov.phi_leading_terms_isBigO (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) : -- --- STMT ---
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    let P : ℕ → ℝ → ℂ := fun j t =>
      (∑' k : ℕ, ((Nat.factorial (k + j) : ℝ)⁻¹) • (t • (σ • T)) ^ k) (Fin.last m) 0
    let Tp : Mat ℂ (m + 2) (m + 2) := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 0 (fun j' => if j' = Fin.last m then τ else 0) j)
        (fun i' => Fin.lastCases 0 (fun j' => T i' j') j) i
    let Vp : Mat ℂ n (m + 2) := Matrix.of fun i j => Fin.lastCases (w i) (fun j' => V i j') j
    -- (5.6)
    (∀ j : ℕ, (fun t : ℝ => P j t - γ * (σ * t) ^ m / (Nat.factorial (m + j) : ℂ))
      =O[𝓝 0] fun t => t ^ (m + 1)) ∧
    -- (5.7a)
    (∀ p : ℕ, (fun t : ℝ => (∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
        V *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • T)) ^ k) *ᵥ
          Pi.single 0 1) - (τ * (σ * t) * P (p + 1) t) • w) =O[𝓝 0] fun t => t ^ (m + 2)) ∧
    -- (5.7b)
    (∀ p : ℕ, (fun t : ℝ => (∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
        Vp *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + p) : ℝ)⁻¹) • (t • (σ • Tp)) ^ k) *ᵥ
          Pi.single 0 1) - (τ * (σ * t) ^ 2 * P (p + 2) t) • (A *ᵥ w))
        =O[𝓝 0] fun t => t ^ (m + 3)) := by -- --- PROOF ---
  intro v γ P Tp Vp
  -- (5.6): the Taylor expansion of `φ_j`, whose terms below `m` vanish by (2.3)
  have hcol : ∀ i, ((σ • T) ^ i *ᵥ Pi.single 0 1) (Fin.last m) = σ ^ i * (T ^ i) (Fin.last m) 0 :=
    fun i => by rw [smul_pow, Matrix.mulVec_single_one]; rfl
  have h56 : ∀ j : ℕ, (fun t : ℝ => P j t - γ * (σ * t) ^ m / (Nat.factorial (m + j) : ℂ))
      =O[𝓝 0] fun t => t ^ (m + 1) := by
    intro j
    have h := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 1) => ℂ)
      (Fin.last m)).isBigO_comp _ (𝓝 0)).trans
      (Krylov.phi_smul_mulVec_taylor_isBigO (σ • T) (Pi.single 0 1) j (m + 1))
    -- only the term `i = m` survives
    refine h.congr_left fun t => ?_
    simp only [ContinuousLinearMap.proj_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      hcol]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      rw [Krylov.hessenberg_pow_apply_eq_zero T hH i (Fin.last m) 0
        (by simp only [Fin.val_zero, Fin.val_last, zero_add]; exact Finset.mem_range.1 hi),
        mul_zero, smul_zero], zero_add, Krylov.hessenberg_pow_apply_last_eq_prod T hH,
      Matrix.mulVec_single_one, Complex.real_smul]
    show P j t - _ = _
    push_cast
    rw [mul_pow]
    field_simp
    rfl
  -- `(cσt)ᵏ(e(t)u) = O(tᵏ t^{m+1})`
  have hlead : ∀ (c : ℂ) (k : ℕ) (u : Fin n → ℂ) (e : ℝ → ℂ),
      (e =O[𝓝 0] fun t => t ^ (m + 1)) →
        (fun t : ℝ => (c * (σ * t) ^ k) • (e t • u)) =O[𝓝 0] fun t => t ^ (m + 1 + k) := by
    intro c k u e he
    have hk : (fun t : ℝ => c * (σ * t) ^ k) =O[𝓝 0] fun t => t ^ k :=
      IsBigO.of_bound (‖c‖ * ‖σ‖ ^ k) (Eventually.of_forall fun t => le_of_eq (by
        rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, mul_pow, norm_pow]; ring))
    have hu := ((ContinuousLinearMap.toSpanSingleton ℂ u).isBigO_comp _ (𝓝 0)).trans he
    refine (hk.smul hu).trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => le_of_eq ?_))
    rw [smul_eq_mul, ← pow_add, one_mul, add_comm k]
  refine ⟨h56, fun p => ?_, fun p => ?_⟩
  · -- (5.7a): (4.4a) and (5.6) at `j = p + 1`
    have h1 := Krylov.phi_error_sub_leading_isBigO A V T τ σ w hH hK p
    dsimp only at h1
    have h2 := hlead τ 1 w _ (h56 (p + 1))
    refine (h1.sub h2).congr_left fun t => ?_
    have hs : τ * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1 + p) : ℂ) =
        τ * (σ * t) ^ 1 * (γ * (σ * t) ^ m / (Nat.factorial (m + (p + 1)) : ℂ)) := by
      rw [show m + 1 + p = m + (p + 1) by ring]
      ring
    rw [hs, smul_smul, mul_sub, sub_smul, pow_one]
    abel
  · -- (5.7b): (5.9a), as (4.4a) for `AV⁺ = V⁺T⁺ + (Av_{m+1})e_{m+1}*`, and (5.6) at `j = p + 2`
    obtain ⟨hKp, hHp, hγp, hvp⟩ := Krylov.correctedKrylov_identity A V T τ w hH hK
    have h1 := Krylov.phi_error_sub_leading_isBigO A Vp Tp 1 σ (A *ᵥ w) hHp hKp p
    dsimp only at h1
    rw [hγp, hvp] at h1
    have h2 := hlead τ 2 (A *ᵥ w) _ (h56 (p + 2))
    refine (h1.sub h2).congr_left fun t => ?_
    have hs : 1 * (γ * τ) * (σ * t) ^ (m + 1 + 1) / (Nat.factorial (m + 1 + 1 + p) : ℂ) =
        τ * (σ * t) ^ 2 * (γ * (σ * t) ^ m / (Nat.factorial (m + (p + 2)) : ℂ)) := by
      rw [show m + 1 + 1 + p = m + (p + 2) by ring]
      ring
    rw [hs, smul_smul, mul_sub, sub_smul]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

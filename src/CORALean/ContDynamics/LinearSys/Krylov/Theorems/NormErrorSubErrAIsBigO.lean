import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorSubLeadingIsBigO
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Err_a is asymptotically correct

[1, Prop. 3]: `‖L_m(t)v‖₂ = τ_{m+1,m}γ_m t^m/m! + O(t^{m+1})` (3.7) as `t → 0`. As in [1]: the
norms of `L_m(t)v` and of the leading term `τ_{m+1,m}γ_m(σt)^m/m! v_{m+1}` of `Prop. 1` differ by
at most the norm of the remainder, and the leading term has norm `τ_{m+1,m}|γ_m| t^m/m!` for
`|σ| = 1`, `‖v_{m+1}‖₂ = 1`, `τ_{m+1,m} ≥ 0` and `t ≥ 0`, the step sizes of [1]; so `t → 0`
from above. No hypothesis on `A`.

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

/-- [1, Prop. 3]: `‖e^{tσA}v - V_me^{tσT_m}e₁‖₂ - τ_{m+1,m}|γ_m| t^m/m! = O(t^{m+1})` as
`t → 0⁺`, under (2.2), upper Hessenberg `T_m`, `v = V_me₁`, `|σ| = 1`, `‖v_{m+1}‖₂ = 1`; `V_m`
has `m + 1` columns here. -/
theorem Krylov.norm_error_sub_errA_isBigO (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℝ) (σ : ℂ) (w : Fin n → ℂ)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + (τ : ℂ) • vecMulVec w (Pi.single (Fin.last m) 1)) (hτ : 0 ≤ τ)
    (hσ : ‖σ‖ = 1) (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ = 1) :
    let v := V *ᵥ Pi.single 0 1
    let γ := ∏ j : Fin m, T j.succ j.castSucc
    (fun t : ℝ => ‖(WithLp.toLp 2 (exp (t • (σ • A)) *ᵥ v -
        V *ᵥ (exp (t • (σ • T)) *ᵥ Pi.single 0 1)) : EuclideanSpace ℂ (Fin n))‖ -
        τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
      =O[𝓝[≥] 0] fun t => t ^ (m + 2) := by -- --- PROOF ---
  intro v γ
  set E := (EuclideanSpace.equiv (Fin n) ℂ).symm with hE
  set a : ℝ → Fin n → ℂ := fun t =>
    exp (t • (σ • A)) *ᵥ v - V *ᵥ (exp (t • (σ • T)) *ᵥ Pi.single 0 1) with ha
  set b : ℝ → Fin n → ℂ := fun t =>
    ((τ : ℂ) * γ * (σ * t) ^ (m + 1) / (Nat.factorial (m + 1) : ℂ)) • w with hb
  -- `Prop. 1`, in the 2-norm
  have h1 := ((E : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).isBigO_comp _ (𝓝 0)).trans
    (Krylov.error_sub_leading_isBigO A V T τ σ w hH hK)
  -- `|‖a‖ - ‖b‖| ≤ ‖a - b‖`, and `‖b(t)‖₂ = τ|γ|t^m/m!` for `t ≥ 0`
  have hb' : ∀ t : ℝ, 0 ≤ t →
      ‖E (b t)‖ = τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
    intro t ht
    show ‖WithLp.toLp 2 (b t)‖ = _
    rw [hb, WithLp.toLp_smul, norm_smul, hw, mul_one, norm_div, norm_mul, norm_mul, norm_pow,
      norm_mul, hσ, one_mul, Complex.norm_of_nonneg hτ, Complex.norm_real, Real.norm_of_nonneg ht,
      Complex.norm_natCast]
  have h2 : (fun t : ℝ => ‖E (a t)‖ - τ * ‖γ‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
      =O[𝓝[≥] 0] fun t => E (a t - b t) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hb' t ht, one_mul, Real.norm_eq_abs, map_sub]
    exact abs_norm_sub_norm_le _ _
  exact h2.trans (h1.mono nhdsWithin_le_nhds)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

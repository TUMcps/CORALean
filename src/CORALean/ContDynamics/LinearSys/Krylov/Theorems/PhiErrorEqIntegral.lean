module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.PhiSeriesEqIntegral
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The Krylov error of a φ-function as an average of exponential errors

[1, Thm. 2]'s step from (4.1b): `L^p_m(t)v = φ_p(σtA)v - V_mφ_p(σtT_m)e₁` (4.3) is
`1/(p - 1)! ∫₀¹(1 - θ)^{p-1}L_m(θt)v dθ` for `p ≥ 1`, `L_m(s)v = e^{σsA}v - V_me^{σsT_m}e₁` the
error of the exponential (2.7). (4.1b) at the matrices `tσA` and `tσT_m`, carried through the
continuous linear maps `B ↦ Bv` and `B ↦ V_mBe₁`, which commute with the integral. `φ_p` is the
series (4.1a); `p ≥ 1` is written `p + 1`. No hypothesis on `A`, `V_m` or `T_m`.

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

/-- [1, Thm. 2]'s step: `φ_{p+1}(tσA)v - V_mφ_{p+1}(tσT_m)e₁ = 1/p! ∫₀¹(1 - θ)ᵖL_m(θt)v dθ`,
`φ_{p+1}` the series (4.1a), `L_m(s)v = e^{sσA}v - V_me^{sσT_m}e₁`. -/
theorem Krylov.phi_error_eq_integral (A : Mat ℂ n n) (V : Mat ℂ n m) (T : Mat ℂ m m) (σ : ℂ)
    (v : Fin n → ℂ) (e : Fin m → ℂ) (p : ℕ) (t : ℝ) : -- --- CONCL ---
    (∑' k : ℕ, ((Nat.factorial (k + (p + 1)) : ℝ)⁻¹) • (t • (σ • A)) ^ k) *ᵥ v -
        V *ᵥ ((∑' k : ℕ, ((Nat.factorial (k + (p + 1)) : ℝ)⁻¹) • (t • (σ • T)) ^ k) *ᵥ e) =
      ((Nat.factorial p : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p •
        (exp ((θ * t) • (σ • A)) *ᵥ v -
          V *ᵥ (exp ((θ * t) • (σ • T)) *ᵥ e)) := by -- --- PROOF ---
  -- `B ↦ Bv` and `B ↦ V_mBe`, continuous and ℝ-linear
  let Φ : Mat ℂ n n →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap
    { toFun := fun B => B *ᵥ v
      map_add' := fun B C => Matrix.add_mulVec B C v
      map_smul' := fun r B => by rw [Matrix.smul_mulVec, RingHom.id_apply] }
  let Ψ : Mat ℂ m m →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap
    { toFun := fun B => V *ᵥ (B *ᵥ e)
      map_add' := fun B C => by rw [Matrix.add_mulVec, Matrix.mulVec_add]
      map_smul' := fun r B => by
        rw [Matrix.smul_mulVec, RingHom.id_apply, Matrix.mulVec_smul] }
  have hint : ∀ {k : ℕ} (M : Mat ℂ k k), Continuous fun θ : ℝ => (1 - θ) ^ p • exp (θ • M) :=
    fun M => (continuous_const.sub continuous_id).pow p |>.smul
      (exp_continuous.comp (continuous_id.smul continuous_const))
  -- (4.1b) at `tσA` and `tσT_m`
  have h1 : ∀ {k : ℕ} (M : Mat ℂ k k),
      (∑' j : ℕ, ((Nat.factorial (j + (p + 1)) : ℝ)⁻¹) • M ^ j) =
        ((Nat.factorial p : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p • exp (θ • M) := fun M =>
    (Krylov.phi_series_eq_integral M).2 p
  rw [h1, h1]
  -- through `B ↦ Bv`, which commutes with the integral
  have hA : (((Nat.factorial p : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p • exp (θ • (t • (σ • A))))
      *ᵥ v = ((Nat.factorial p : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p •
        (exp ((θ * t) • (σ • A)) *ᵥ v) := by
    show Φ _ = _
    rw [Φ.map_smul]
    congr 1
    refine (Φ.intervalIntegral_comp_comm ((hint _).intervalIntegrable 0 1)).symm.trans ?_
    refine intervalIntegral.integral_congr fun θ _ => ?_
    show ((1 - θ) ^ p • exp (θ • (t • (σ • A)))) *ᵥ v = _
    rw [Matrix.smul_mulVec, smul_smul]
  -- and through `B ↦ V_mBe`
  have hT : V *ᵥ ((((Nat.factorial p : ℝ)⁻¹) • ∫ θ in (0 : ℝ)..1,
      (1 - θ) ^ p • exp (θ • (t • (σ • T)))) *ᵥ e) = ((Nat.factorial p : ℝ)⁻¹) •
        ∫ θ in (0 : ℝ)..1, (1 - θ) ^ p • (V *ᵥ (exp ((θ * t) • (σ • T)) *ᵥ e)) := by
    show Ψ _ = _
    rw [Ψ.map_smul]
    congr 1
    refine (Ψ.intervalIntegral_comp_comm ((hint _).intervalIntegrable 0 1)).symm.trans ?_
    refine intervalIntegral.integral_congr fun θ _ => ?_
    show V *ᵥ (((1 - θ) ^ p • exp (θ • (t • (σ • T)))) *ᵥ e) = _
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  -- one integral of the difference
  have hE : ∀ {k : ℕ} (M : Mat ℂ k k), Continuous fun θ : ℝ => exp ((θ * t) • M) :=
    fun M => exp_continuous.comp ((continuous_id.mul continuous_const).smul continuous_const)
  rw [hA, hT, ← smul_sub, ← intervalIntegral.integral_sub]
  · simp only [smul_sub]
  · exact (((continuous_const.sub continuous_id).pow p).smul
      ((hE _).matrix_mulVec continuous_const)).intervalIntegrable _ _
  · exact (((continuous_const.sub continuous_id).pow p).smul
      (continuous_const.matrix_mulVec
        ((hE _).matrix_mulVec continuous_const))).intervalIntegrable _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

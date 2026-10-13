import CORALean.Global.Tensor
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Basic

/-!
# The Taylor expansion of `e^{tN}x` at `t = 0`

`e^{tN}x = Σ_{j<p} tʲ/j! Nʲx + O(tᵖ)` as `t → 0`, the expansion behind [1, Eq. 2.10] and
the asymptotics (2.12) and (3.7). Mathlib's exponential has its series as power series at `0`
with infinite radius, so `exp(y) - Σ_{j<p} yʲ/j! = O(‖y‖ᵖ)`; at `y = tN`, and through the
continuous linear map `B ↦ Bx`, this is `O(tᵖ)`. The vector space `Fin k → ℂ` carries its sup
norm; `O(·)` does not depend on the norm in finite dimension.

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

variable {k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.10]'s step: `e^{tN}x - Σ_{j<p} tʲ/j! Nʲx = O(tᵖ)` as `t → 0`, for a complex
matrix `N`. -/
theorem Krylov.exp_smul_mulVec_taylor_isBigO (N : Mat ℂ k k) (x : Fin k → ℂ) (p : ℕ) :
    (fun t : ℝ => exp (t • N) *ᵥ x -
        ∑ j ∈ Finset.range p, ((Nat.factorial j : ℂ)⁻¹ * (t : ℂ) ^ j) • (N ^ j *ᵥ x))
      =O[𝓝 0] fun t => t ^ p := by -- --- PROOF ---
  -- the power series of `exp` at `0`, of infinite radius
  have h := (hasFPowerSeriesAt_exp_zero_of_radius_pos (𝕂 := ℝ) (𝔸 := Mat ℂ k k)
    (by simp [expSeries_radius_eq_top])).isBigO_sub_partialSum_pow p
  have hc : Tendsto (fun t : ℝ => t • N) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const N
  have h2 := h.comp_tendsto hc
  -- `‖tN‖ᵖ ≤ ‖N‖ᵖ |t|ᵖ`
  have h3 : (fun t : ℝ => ‖t • N‖ ^ p) =O[𝓝 0] fun t => t ^ p := by
    refine IsBigO.of_bound (‖N‖ ^ p) (Eventually.of_forall fun t => ?_)
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity), norm_pow, mul_comm]
  -- `B ↦ Bx` is continuous linear
  let L : Mat ℂ k k →ₗ[ℝ] (Fin k → ℂ) :=
    { toFun := fun B => B *ᵥ x
      map_add' := fun B C => Matrix.add_mulVec B C x
      map_smul' := fun r B => by rw [Matrix.smul_mulVec, RingHom.id_apply] }
  have h4 := ((LinearMap.toContinuousLinearMap L).isBigO_comp _ (𝓝 0)).trans (h2.trans h3)
  refine h4.congr_left fun t => ?_
  show (exp (0 + t • N) - (expSeries ℝ (Mat ℂ k k)).partialSum p (t • N)) *ᵥ x = _
  simp only [zero_add, FormalMultilinearSeries.partialSum, expSeries_apply_eq, Matrix.sub_mulVec,
    Matrix.sum_mulVec, smul_pow, smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mulVec]
  ext i
  simp [Complex.real_smul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

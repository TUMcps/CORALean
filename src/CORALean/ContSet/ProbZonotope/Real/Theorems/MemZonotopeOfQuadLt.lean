module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.SqrtMulVecMemZonotope
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# The open `m`-sigma ellipsoid around a mean lies in the confidence set

For a positive definite covariance and a mean `μ` of `P`, every `y` with
`(y - μ)ᵀ Σ⁻¹ (y - μ) < m²` is in `zonotope(probZ, m)`: with `g` the symmetric square root of
`Σ`, `u = g⁻¹ (y - μ)` has `‖u‖² = (y - μ)ᵀ Σ⁻¹ (y - μ) < m²`, so every coefficient is
within `m`, and `y = μ + g u`. The confidence zonotope is therefore at least as large as the
ellipsoid whose boundary `max(probZ, m)` measures.

## Inputs
* `P` – probabilistic zonotope
* `μ` – mean of length `n`
* `m` – real number
* `y` – vector of length `n`

## Hypotheses
* `hP` – `P.cov.PosDef`
* `hμ` – `μ` lies in `P.Z`
* `hm` – `0 ≤ m`
* `hy` – `y` is less than `m` sigmas from `μ`

## Conclusion
* the open `m`-sigma ellipsoid around a mean lies in the confidence set
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.mem_zonotope_of_quad_lt (P : ProbZonotope n) (hP : P.cov.PosDef)
    {μ : Vec ℝ n} (hμ : μ ∈ P.Z.construct) {m : ℝ} (hm : 0 ≤ m) {y : Vec ℝ n}
    (hy : (y - μ) ⬝ᵥ P.cov⁻¹ *ᵥ (y - μ) < m ^ 2) : -- --- CONCL ---
    y ∈ (P.zonotope m).construct := by -- --- PROOF ---
  -- the symmetric square root `B` of the covariance, invertible
  set B := CFC.sqrt P.cov with hBdef
  have hBB : B * B = P.cov := CFC.sqrt_mul_sqrt_self P.cov hP.posSemidef.nonneg
  have hBt : Bᵀ = B := by
    have := (CFC.sqrt_nonneg P.cov).isSelfAdjoint
    simpa [IsSelfAdjoint, star_eq_conjTranspose] using this
  have hdet : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB
    rw [det_mul, h0, zero_mul] at this
    exact hP.det_pos.ne this
  have hBu : IsUnit B := (isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hdet)
  set d := y - μ with hd
  set u := B⁻¹ *ᵥ d with hu
  have hBinv_t : (B⁻¹)ᵀ = B⁻¹ := by rw [transpose_nonsing_inv, hBt]
  -- the quadratic form is the squared norm of `u`
  have hvm : d ᵥ* B⁻¹ = B⁻¹ *ᵥ d := by
    conv_lhs => rw [← hBinv_t]
    exact vecMul_transpose _ _
  have hq : d ⬝ᵥ P.cov⁻¹ *ᵥ d = u ⬝ᵥ u := by
    rw [← hBB, Matrix.mul_inv_rev, ← mulVec_mulVec, dotProduct_mulVec, hu, hvm]
  rw [hq] at hy
  -- `m` is positive, as `‖u‖² < m²`
  have hm2 : 0 < m := by
    rcases hm.eq_or_lt with h | h
    · rw [← h] at hy
      exact absurd hy (not_lt.2 (by simpa using dotProduct_self_star_nonneg u))
    · exact h
  -- every coefficient of `u` is within `m`, so `y = μ + B u` is in the confidence set
  have hcoef : ∀ j, |u j| ≤ m := fun j => by
    have h1 : u j ^ 2 ≤ u ⬝ᵥ u := by
      rw [dotProduct]
      simpa [sq] using Finset.single_le_sum (f := fun i => u i * u i)
        (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ j)
    exact abs_le_of_sq_le_sq (by nlinarith) hm2.le
  have key := P.add_sqrt_mulVec_mem_zonotope hμ hm2 hcoef
  have hy' : y = μ + B *ᵥ u := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).1 hBu), one_mulVec, hd]
    abel
  rw [hy']
  exact key

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

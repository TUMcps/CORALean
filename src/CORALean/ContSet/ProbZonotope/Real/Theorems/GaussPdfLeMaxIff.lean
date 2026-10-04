import CORALean.ContSet.ProbZonotope.Real.Operations.Max
import CORALean.ContSet.ProbZonotope.Real.Definitions.GaussPdf

/-!
# `ProbZonotope.max` is the density on the `m`-sigma bound

For a covariance of positive determinant, the density `N(μ, Σ)` at `x` is at most
`max(probZ, m)` exactly when `x` lies on or outside the `m`-sigma ellipsoid,
`m² ≤ (x - μ)ᵀ Σ⁻¹ (x - μ)`; on its boundary it equals it. `max` is therefore not merely an
over-approximation of the maximum there: it is attained.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open WithLp Matrix
open scoped _root_.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.gaussPdf_le_max_iff (P : ProbZonotope n) (hd : 0 < P.cov.det) (c : Vec ℝ n)
    (x : EuclideanSpace ℝ (Fin n)) (m : ℝ) :
    gaussPdf c P.cov x ≤ P.max m
      ↔ m ^ 2 ≤ (ofLp x - c) ⬝ᵥ P.cov⁻¹ *ᵥ (ofLp x - c) := by -- --- PROOF ---
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hK : 0 < (2 * π) ^ (-(n : ℝ) / 2) * P.cov.det ^ (-(1 : ℝ) / 2) := by positivity
  have hmax : P.max m = ((2 * π) ^ (-(n : ℝ) / 2) * P.cov.det ^ (-(1 : ℝ) / 2))
      * Real.exp (-(m ^ 2) / 2) := by
    unfold ProbZonotope.max
    have e1 : (2 * π) ^ (-(n : ℝ) / 2) = ((2 * π) ^ ((n : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg h2π.le]; ring_nf
    have e2 : P.cov.det ^ (-(1 : ℝ) / 2) = (P.cov.det ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg hd.le]; ring_nf
    rw [e1, e2, one_div, mul_inv]
    ring_nf
  unfold gaussPdf
  rw [hmax, mul_le_mul_iff_right₀ hK, Real.exp_le_exp]
  rw [neg_dotProduct]
  constructor <;> intro h <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

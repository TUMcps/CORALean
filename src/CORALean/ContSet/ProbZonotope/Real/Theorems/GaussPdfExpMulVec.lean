module

public import CORALean.ContSet.ProbZonotope.Real.Definitions.GaussPdf
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.DetExpSmul

@[expose] public section

/-!
# The PDF value of a point under the linear flow

`[1, Prop. 3]`: under the map `e^{At}` the PDF value of a point changes by the factor
`e^{-tr(A)t}`: the Gaussian `N(e^{At}c, e^{At} Σ e^{Aᵀt})` the flow carries `N(c, Σ)` to takes
at `x' = e^{At}x` the value `e^{-tr(A)t}` times the value of `N(c, Σ)` at `x`. The paper's
parallelotope-volume argument needs `det(e^{At}) = e^{tr(A)t}` (`MatExp.det_exp_smul`); here the
normalization gives `det(e^{At} Σ e^{Aᵀt})^{-1/2} = e^{-tr(A)t} det(Σ)^{-1/2}` and the quadratic
form is invariant. `Σ` has positive determinant.

## Inputs
* `A` – `n × n` matrix
* `t` – real number
* `c` – center of length `n`
* `S` – `n × n` matrix
* `x` – point

## Hypotheses
* `hS` – `0 < S.det`

## Conclusion
* under `exp(tA)` the Gaussian density at the image point is `exp(-t tr A)` times the density at `x`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open WithLp Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem gaussPdf_exp_mulVec (A : Mat ℝ n n) (t : ℝ) (c : Vec ℝ n) {S : Mat ℝ n n}
    (hS : 0 < S.det) (x : EuclideanSpace ℝ (Fin n)) : -- --- CONCL ---
    gaussPdf (exp (t • A) *ᵥ c) (exp (t • A) * S * (exp (t • A))ᵀ)
        (toLp 2 (exp (t • A) *ᵥ ofLp x))
      = Real.exp (-(t * A.trace)) * gaussPdf c S x := by -- --- PROOF ---
  set E := exp (t • A) with hE
  have hdetE : E.det = Real.exp (t * A.trace) := CORALean.MatExp.det_exp_smul A t
  have hEne : E.det ≠ 0 := by rw [hdetE]; exact (Real.exp_pos _).ne'
  have hEu : IsUnit E.det := isUnit_iff_ne_zero.mpr hEne
  have hdet : (E * S * Eᵀ).det = Real.exp (2 * (t * A.trace)) * S.det := by
    have h2 : Real.exp (2 * (t * A.trace)) = Real.exp (t * A.trace) * Real.exp (t * A.trace) := by
      rw [← Real.exp_add]; ring_nf
    rw [det_mul, det_mul, det_transpose, hdetE, h2]
    ring
  -- the normalization
  have hnorm : (E * S * Eᵀ).det ^ (-(1 : ℝ) / 2)
      = Real.exp (-(t * A.trace)) * S.det ^ (-(1 : ℝ) / 2) := by
    rw [hdet, Real.mul_rpow (Real.exp_pos _).le hS.le, ← Real.exp_mul]
    congr 2
    ring
  -- the quadratic form
  have hinv : (E * S * Eᵀ)⁻¹ = (E⁻¹)ᵀ * S⁻¹ * E⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.transpose_nonsing_inv]
  have hE1 : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hEu
  have hq : ∀ y : Vec ℝ n, (E *ᵥ y) ⬝ᵥ (E * S * Eᵀ)⁻¹ *ᵥ (E *ᵥ y) = y ⬝ᵥ S⁻¹ *ᵥ y := by
    intro y
    have h1 : E⁻¹ *ᵥ (E *ᵥ y) = y := by rw [mulVec_mulVec, hE1, one_mulVec]
    rw [hinv, ← mulVec_mulVec, ← mulVec_mulVec, h1, dotProduct_mulVec, vecMul_transpose, h1]
  unfold gaussPdf
  have e1 : ofLp (toLp 2 (E *ᵥ ofLp x)) - E *ᵥ c = E *ᵥ (ofLp x - c) := by
    simp [mulVec_sub]
  rw [e1, neg_dotProduct, hq, ← neg_dotProduct, hnorm]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

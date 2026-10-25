module

public import CORALean.Global.IpmEllipsoidEq
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# `μ_Q = Tr[PW] + γ²` bounds the mean squared half width

[1, Sec. 3 (Problem 1.b)]: for the ellipsoid class, with `W = E[ϕϕᵀ]`,
"`E[(half width)²] = E[(√(ϕᵀPϕ) + γ)²] ≤ 2E[ϕᵀPϕ + γ²] = 2Tr[PE[ϕϕᵀ]] + 2γ² = 2μ_Q`". The half width
of `I(ϕ)` is `√(ϕᵀPϕ) + γ` by [1, Eq. 7] (`ipmEllipsoid_eq`). The chain is `(u + v)² ≤ 2(u² + v²)`
pointwise, then `E[ϕᵀPϕ] = Σᵢⱼ Pᵢⱼ E[ϕᵢϕⱼ] = Tr[PW]`, for any probability distribution of `ϕ` whose
second moments exist.

## Inputs
* `P` – shape matrix of the ellipsoid
* `γ` – noise bound
* `μ` – distribution of the regressor

## Hypotheses
* `hP` – the shape matrix is positive semidefinite
* `hint` – all second moments of the regressor are integrable

## Conclusion
* the mean squared half width is at most twice the trace cost

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (Problem 1.b)]: `E[(√(ϕᵀPϕ) + γ)²] ≤ 2 (Tr[PW] + γ²)`, `W = E[ϕϕᵀ]`. -/
theorem ipmEllipsoid_mean_sq_halfWidth_le (P : Mat ℝ n n) (hP : P.PosSemidef) (γ : ℝ)
    (μ : Measure (Vec ℝ n)) [IsProbabilityMeasure μ]
    (hint : ∀ i j, Integrable (fun ϕ : Vec ℝ n => ϕ i * ϕ j) μ) : -- --- CONCL ---
    ∫ ϕ, (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ) ^ 2 ∂μ
      ≤ 2 * (Matrix.trace (P * Matrix.of fun i j => ∫ ϕ, ϕ i * ϕ j ∂μ)
        + γ ^ 2) := by -- --- PROOF ---
  -- the quadratic form, as a sum of the second moments' integrands
  have hform : ∀ ϕ : Vec ℝ n, ϕ ⬝ᵥ (P *ᵥ ϕ) = ∑ i, ∑ j, P i j * (ϕ i * ϕ j) := fun ϕ => by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hqint : Integrable (fun ϕ : Vec ℝ n => ϕ ⬝ᵥ (P *ᵥ ϕ)) μ := by
    simp only [hform]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j).const_mul _
  have hq0 : ∀ ϕ : Vec ℝ n, 0 ≤ ϕ ⬝ᵥ (P *ᵥ ϕ) := fun ϕ => by
    simpa using hP.dotProduct_mulVec_nonneg ϕ
  -- `(u + v)² ≤ 2(u² + v²)` with `u² = ϕᵀPϕ`
  have hpt : ∀ ϕ : Vec ℝ n, (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ) ^ 2
      ≤ 2 * (ϕ ⬝ᵥ (P *ᵥ ϕ)) + 2 * γ ^ 2 := fun ϕ => by
    have hs := Real.sq_sqrt (hq0 ϕ)
    nlinarith [sq_nonneg (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) - γ)]
  have hcont : Continuous fun ϕ : Vec ℝ n => (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ) ^ 2 := by
    simp only [hform]
    fun_prop
  have hrhs : Integrable (fun ϕ : Vec ℝ n => 2 * (ϕ ⬝ᵥ (P *ᵥ ϕ)) + 2 * γ ^ 2) μ :=
    (hqint.const_mul 2).add (integrable_const _)
  have hlhs : Integrable (fun ϕ : Vec ℝ n => (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ) ^ 2) μ :=
    hrhs.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ϕ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt ϕ)
  -- `E[ϕᵀPϕ] = Tr[PW]`
  have htr : ∫ ϕ, ϕ ⬝ᵥ (P *ᵥ ϕ) ∂μ
      = Matrix.trace (P * Matrix.of fun i j => ∫ ϕ, ϕ i * ϕ j ∂μ) := by
    simp only [hform]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j).const_mul _]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ϕ => mul_comm _ _)
  calc ∫ ϕ, (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ) ^ 2 ∂μ
      ≤ ∫ ϕ, (2 * (ϕ ⬝ᵥ (P *ᵥ ϕ)) + 2 * γ ^ 2) ∂μ := integral_mono hlhs hrhs hpt
    _ = 2 * (Matrix.trace (P * Matrix.of fun i j => ∫ ϕ, ϕ i * ϕ j ∂μ) + γ ^ 2) := by
      rw [integral_add (hqint.const_mul 2) (integrable_const _), integral_const_mul, htr,
        integral_const, probReal_univ, one_smul]
      ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

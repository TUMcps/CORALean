module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# The inverse of the shape matrix of the outer ellipsoid

[1, Eq. 16]: with `R = Q₁⁻¹ Q₂` and `Q(β) = (1 + 1/β) Q₁ + (1 + β) Q₂`,
`Q(β)⁻¹ = β/(1+β) (I + βR)⁻¹ Q₁⁻¹`. Indeed `Q(β) = ((1+β)/β) Q₁ (I + βR)`, and `I + βR` is
invertible because `Q(β)` is, its determinant being a factor of `det Q(β)`.

## Inputs
* `Q₁` – first shape matrix
* `Q₂` – second shape matrix
* `β` – weight of the shape sum

## Hypotheses
* `h₁` – `Q₁` positive definite
* `h₂` – `Q₂` positive definite
* `hβ` – `0 < β`

## Conclusion
* the inverse of `Q(β)` is `β/(1+β)` times `(I + βR)⁻¹ Q₁⁻¹`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 16]: `Q(β)⁻¹ = β/(1+β) · (I + βR)⁻¹ Q₁⁻¹`, for positive-definite `Q₁`, `Q₂`. -/
theorem Ellipsoid.halder_inv_shape {Q₁ Q₂ : Matrix n n ℝ} (h₁ : Q₁.PosDef)
    (h₂ : Q₂.PosDef) {β : ℝ} (hβ : 0 < β) : -- --- CONCL ---
    ((1 + 1 / β) • Q₁ + (1 + β) • Q₂)⁻¹
      = (β / (1 + β)) • ((1 + β • (Q₁⁻¹ * Q₂))⁻¹ * Q₁⁻¹) := by -- --- PROOF ---
  have hu₁ : IsUnit Q₁.det := (isUnit_iff_isUnit_det Q₁).1 h₁.isUnit
  have hQ : Q₁ * (Q₁⁻¹ * Q₂) = Q₂ := by
    rw [← mul_assoc, mul_nonsing_inv Q₁ hu₁, one_mul]
  set M : Matrix n n ℝ := 1 + β • (Q₁⁻¹ * Q₂) with hM
  -- `Q(β) = ((1+β)/β) • (Q₁ M)`
  have hfac : (1 + 1 / β) • Q₁ + (1 + β) • Q₂ = ((1 + β) / β) • (Q₁ * M) := by
    rw [hM, mul_add, mul_one, mul_smul_comm, hQ, smul_add, smul_smul]
    have h1 : (1 + β) / β = 1 + 1 / β := by field_simp; ring
    have h2 : (1 + β) / β * β = 1 + β := by field_simp
    rw [h2, h1]
  have hQpd : ((1 + 1 / β) • Q₁ + (1 + β) • Q₂).PosDef :=
    (h₁.smul (by positivity)).add (h₂.smul (by positivity))
  -- `M` is invertible because `Q(β)` is
  have hMu : IsUnit M.det := by
    have hd := (isUnit_iff_isUnit_det _).1 hQpd.isUnit
    rw [hfac, det_smul, det_mul] at hd
    exact (IsUnit.mul_iff.1 (IsUnit.mul_iff.1 hd).2).2
  refine inv_eq_right_inv ?_
  rw [hfac, smul_mul_assoc, mul_smul_comm, smul_smul]
  calc (((1 + β) / β) * (β / (1 + β))) • (Q₁ * M * (M⁻¹ * Q₁⁻¹))
      = (Q₁ * (M * M⁻¹) * Q₁⁻¹) := by
        rw [show ((1 + β) / β) * (β / (1 + β)) = 1 by field_simp, one_smul]
        simp only [mul_assoc]
    _ = 1 := by rw [mul_nonsing_inv M hMu, mul_one, mul_nonsing_inv Q₁ hu₁]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

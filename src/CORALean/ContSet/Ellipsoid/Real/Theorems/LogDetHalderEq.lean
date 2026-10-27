module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderEigenvalues
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLogDet

@[expose] public section

/-!
# The volume criterion is the sum over the eigenvalues

For positive-definite `Q₁`, `Q₂` and the positive eigenvalues `λᵢ` of `R = Q₁⁻¹ Q₂ = S Λ T`,
`log det((1 + 1/β) Q₁ + (1 + β) Q₂) = log det Q₁ + ∑ᵢ log((1 + 1/β) + (1 + β) λᵢ)` for
every `β > 0`, for any diagonalization `R = S Λ T`: with
`Q(β) = Q₁ ((1 + 1/β) I + (1 + β) R)` and `R = S Λ S⁻¹`, the determinant of the second
factor is the product. This is what turns the objective `log det Q(β)` of
[1, Eq. 14] into the scalar function that [1, Eq. 18] differentiates.

## Inputs
* `Q₁` – first shape matrix
* `Q₂` – second shape matrix

## Hypotheses
* `h₁` – `Q₁` positive definite
* `h₂` – `Q₂` positive definite

## Conclusion
* `log det Q(β)` is `log det Q₁` plus a sum over the eigenvalues

## References

* [1] [A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/halder-cdc-minkowski-sum-ellipsoids.md)
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

/-- [1, Eq. 14]: `log det Q(β) = log det Q₁ + ∑ᵢ log((1 + 1/β) + (1 + β) λᵢ)`, `λᵢ > 0`. -/
theorem Ellipsoid.log_det_halder_eq {Q₁ Q₂ : Matrix n n ℝ} (h₁ : Q₁.PosDef)
    (h₂ : Q₂.PosDef) : -- --- CONCL ---
    ∃ (S T : Matrix n n ℝ) (lam : n → ℝ), S * T = 1 ∧ T * S = 1 ∧
      Q₁⁻¹ * Q₂ = S * diagonal lam * T ∧ (∀ i, 0 < lam i) ∧ ∀ β : ℝ, 0 < β →
      Real.log (((1 + 1 / β) • Q₁ + (1 + β) • Q₂).det)
        = Real.log Q₁.det + Ellipsoid.halderLogDet lam β := by -- --- PROOF ---
  obtain ⟨S, T, lam, hST, hTS, hR, hpos⟩ := Ellipsoid.halder_eigenvalues h₁ h₂
  refine ⟨S, T, lam, hST, hTS, hR, hpos, fun β hβ => ?_⟩
  have hdet₁ : 0 < Q₁.det := h₁.det_pos
  -- `Q₂ = Q₁ R` and `R = S Λ T`
  have hQ : Q₂ = Q₁ * (S * diagonal lam * T) := by
    rw [← hR, ← mul_assoc, mul_nonsing_inv Q₁ (isUnit_iff_isUnit_det Q₁ |>.1 h₁.isUnit), one_mul]
  -- so `Q(β) = Q₁ S diag((1+1/β) + (1+β)λᵢ) T`
  have hfac : (1 + 1 / β) • Q₁ + (1 + β) • Q₂
      = Q₁ * (S * diagonal (fun i => (1 + 1 / β) + (1 + β) * lam i) * T) := by
    have h1 : S * diagonal (fun i => (1 + 1 / β) + (1 + β) * lam i) * T
        = (1 + 1 / β) • (1 : Matrix n n ℝ) + (1 + β) • (S * diagonal lam * T) := by
      have : (diagonal (fun i => (1 + 1 / β) + (1 + β) * lam i) : Matrix n n ℝ)
          = (1 + 1 / β) • (1 : Matrix n n ℝ) + (1 + β) • diagonal lam := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [this, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
        mul_one, hST]
    rw [h1, mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← hQ]
  -- the determinant is `det Q₁` times the product, as `det S det T = 1`
  rw [hfac, det_mul, det_mul, det_mul, det_diagonal]
  have hSdet : S.det * T.det = 1 := by rw [← det_mul, hST, det_one]
  have hprodpos : ∀ i, 0 < (1 + 1 / β) + (1 + β) * lam i := fun i => by
    have := hpos i; positivity
  have : Q₁.det * ((S.det * ∏ i, ((1 + 1 / β) + (1 + β) * lam i)) * T.det)
      = Q₁.det * ∏ i, ((1 + 1 / β) + (1 + β) * lam i) := by
    generalize (∏ i, ((1 + 1 / β) + (1 + β) * lam i)) = P
    calc Q₁.det * ((S.det * P) * T.det) = Q₁.det * P * (S.det * T.det) := by ring
      _ = Q₁.det * P := by rw [hSdet, mul_one]
  rw [this, Real.log_mul hdet₁.ne' (Finset.prod_pos fun i _ => hprodpos i).ne',
    Real.log_prod fun i _ => (hprodpos i).ne']
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

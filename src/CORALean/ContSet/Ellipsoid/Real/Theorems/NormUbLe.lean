module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.NormUb
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose

@[expose] public section

/-!
# The Euclidean norm of a point of an ellipsoid is at most `Ellipsoid.normUb`

`‖q + G u‖₂ ≤ ‖q‖₂ + ‖G u‖₂`, and the Frobenius norm of `G = Q^(1/2)`, which is `sqrt(trace Q)`,
bounds `‖G u‖₂` for `‖u‖₂ ≤ 1` (Cauchy-Schwarz on each row). An outer bound; it is not tight in
general.

## Inputs
* `E` – ellipsoid
* `x` – point

## Hypotheses
* `hx` – `x` in `E`

## Conclusion
* the norm of `x` is at most `normUb`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Frobenius norm bounds the Euclidean operator norm. -/
theorem aux_norm₂_mulVec_le_frobenius_ellipsoid (M : Mat ℝ m n) (y : Vec ℝ n) : -- --- CONCL ---
    ‖M.mulVec y‖₂ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * ‖y‖₂ := by -- --- PROOF ---
  have hF : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [norm₂, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (norm₂_nonneg _), ?_⟩
  have hsq : (Real.sqrt (∑ i, ∑ j, M i j ^ 2) * ‖y‖₂) ^ 2 =
      (∑ i, ∑ j, M i j ^ 2) * ∑ j, y j ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hF, norm₂_sq]
  rw [hsq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) y
  simpa [Matrix.mulVec, dotProduct] using this


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.norm₂_le_normUb (E : Ellipsoid n) {x : Vec ℝ n}
    (hx : x ∈ E.construct) : -- --- CONCL ---
    ‖x‖₂ ≤ E.normUb := by -- --- PROOF ---
  -- the ellipsoid as `q + G u`, `‖u‖₂ ≤ 1`
  simp only [Ellipsoid.construct_eq_sqrt] at *
  obtain ⟨u, hu, rfl⟩ := hx
  refine le_trans (norm₂_add_le _ _) (add_le_add le_rfl ?_)
  -- the squared Frobenius norm of `G` is `trace (G Gᵀ) = trace Q`
  have htr : ∑ i, ∑ j, E.G i j ^ 2 = E.Q.trace := by
    rw [← E.G_mul_transpose]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  refine le_trans (aux_norm₂_mulVec_le_frobenius_ellipsoid E.G u) ?_
  rw [htr]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

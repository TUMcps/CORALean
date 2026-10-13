import CORALean.ContSet.Capsule.Real.Operations.Mtimes
import CORALean.Global.EuclideanNorm
import Mathlib.Algebra.Order.Chebyshev

/-!
# `Capsule.mtimes` encloses the image

`‖M y‖₂ ≤ ‖M‖_F ‖y‖₂`: each coordinate of `M y` is a row's dot product with `y`, bounded by
Cauchy–Schwarz, and the squares add up to the Frobenius norm. So the linear image of a point
`c + t g + b` of the capsule is the segment point `M c + t (M g)` plus a remainder `M b` of
length at most `‖M‖_F r`. Outer only: the image is a segment thickened by an ellipsoid.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Frobenius norm bounds the Euclidean operator norm. -/
theorem aux_norm₂_mulVec_le_frobenius (M : Mat ℝ m n) (y : Vec ℝ n) :
    ‖M.mulVec y‖₂ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * ‖y‖₂ := by -- --- PROOF ---
  have hF : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
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

/-- The linear image of a capsule lies in `Capsule.mtimes`. -/
theorem Capsule.mtimes_outer (M : Mat ℝ m n) (C : Capsule n) :
    (fun x => M.mulVec x) '' C.construct ⊆ (C.mtimes M).construct := by -- --- PROOF ---
  rintro _ ⟨x, ⟨t, ht, hx⟩, rfl⟩
  refine ⟨t, ht, ?_⟩
  have hb : ‖x - (C.c + t • C.g)‖₂ ≤ C.r := hx
  have heq : M.mulVec x - (M.mulVec C.c + t • M.mulVec C.g) = M.mulVec (x - (C.c + t • C.g)) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]
  change ‖M.mulVec x - (M.mulVec C.c + t • M.mulVec C.g)‖₂ ≤ C.r * Real.sqrt (∑ i, ∑ j, M i j ^ 2)
  rw [heq]
  calc _ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * ‖x - (C.c + t • C.g)‖₂ :=
        aux_norm₂_mulVec_le_frobenius _ _
    _ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) * C.r := by gcongr
    _ = _ := mul_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

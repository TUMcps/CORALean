import CORALean.ContSet.Zonotope.Real.Operations.ReduceScottStep

/-!
# (A.10) keeps every generator not removed

[1, Sec. 4.3 (new reduction)]: after `T := T(I + diag|r|)` and `R := (I + diag|r|)⁻¹R₋`, "`Z̃` can
be recovered after the update as `Z̃ = {[T TR], c}`". That needs `T'R'` to be the kept generators
`V₋`, and it is: `T(I + diag|r|)(I + diag|r|)⁻¹ r_l = T r_l` for every kept column `r_l`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: `T'r'_l = T r_l`, the kept generators unchanged by the update. -/
theorem Zonotope.reduceScottStep_mulVec {n k : ℕ} (T : Mat ℝ n n) (R : Fin (k + 1) → Vec ℝ n)
    (ind : Fin (k + 1)) (l : Fin k) :
    (Zonotope.reduceScottStep T R ind).1 *ᵥ (Zonotope.reduceScottStep T R ind).2 l
      = T *ᵥ R (ind.succAbove l) := by -- --- PROOF ---
  show (T * diagonal fun i => 1 + |R ind i|)
      *ᵥ ((diagonal fun i => (1 + |R ind i|)⁻¹) *ᵥ R (ind.succAbove l))
    = T *ᵥ R (ind.succAbove l)
  rw [← Matrix.mulVec_mulVec]
  congr 1
  funext i
  have hpos : (0 : ℝ) < 1 + |R ind i| := by positivity
  simp [Matrix.mulVec_diagonal, mul_inv_cancel_left₀ hpos.ne']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

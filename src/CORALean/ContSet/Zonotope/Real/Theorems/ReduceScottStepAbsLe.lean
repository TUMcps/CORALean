import CORALean.ContSet.Zonotope.Real.Operations.ReduceScottStep

/-!
# (A.10) keeps the entries of `R` within `[-1, 1]`

[1, Sec. 4.3 (new reduction)]: "the updated `R` matrix retains the property that every element is
less than one, since the elements of `(I + diag|r|)` are greater than one". Row `i` of `R₋` is
divided by `1 + |r_i| ≥ 1`, which never increases an absolute value. This is what lets the next step
read `‖r‖∞ ≤ 1` off the state again without a new factorization.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: `|R_li| ≤ 1` everywhere before the update gives the same after
it. -/
theorem Zonotope.reduceScottStep_abs_le {n k : ℕ} (T : Mat ℝ n n) (R : Fin (k + 1) → Vec ℝ n)
    (ind : Fin (k + 1)) (hR : ∀ l i, |R l i| ≤ 1) (l : Fin k) (i : Fin n) :
    |(Zonotope.reduceScottStep T R ind).2 l i| ≤ 1 := by -- --- PROOF ---
  show |((diagonal fun i => (1 + |R ind i|)⁻¹) *ᵥ R (ind.succAbove l)) i| ≤ 1
  have hpos : (0 : ℝ) < 1 + |R ind i| := by positivity
  rw [Matrix.mulVec_diagonal, abs_mul, abs_inv, abs_of_pos hpos]
  calc (1 + |R ind i|)⁻¹ * |R (ind.succAbove l) i| ≤ 1 * 1 := by
        gcongr
        · exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (R ind i)])
        · exact hR _ _
    _ = 1 := one_mul 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

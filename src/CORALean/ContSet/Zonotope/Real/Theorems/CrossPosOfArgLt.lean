module

public import CORALean.ContSet.Zonotope.Real.Theorems.CrossEqNormMulSin

@[expose] public section

/-!
# A strictly smaller angle gives a positive cross product

The strict form of `Zonotope.cross_nonneg_of_arg_le`, for nonzero vectors of the upper half-plane
`y > 0 ∨ (y = 0 ∧ x ≥ 0)`, whose angles lie in `[0, π)`. It is what makes the pivot split of
[1, Alg. 4] progress: the sum of the cross products with the pivot is zero, so they cannot all be
positive.

## Inputs
* `u` – first planar vector
* `w` – second planar vector

## Hypotheses
* `hu` – `u` has nonnegative height
* `hw` – `w` points upward
* `hu0` – `u` nonzero
* `hw0` – `w` nonzero
* `h` – angle of `u` below that of `w`

## Conclusion
* the cross product is positive

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A nonzero vector has positive norm as a complex number. -/
theorem Zonotope.aux_norm_pos {u : Vec ℝ 2} (hu : u ≠ 0) : -- --- CONCL ---
    0 < ‖(⟨u 0, u 1⟩ : ℂ)‖ := by -- --- PROOF ---
  rw [norm_pos_iff]
  intro hc
  apply hu
  ext i
  fin_cases i
  · exact congrArg Complex.re hc
  · exact congrArg Complex.im hc


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cross_pos_of_arg_lt {u w : Vec ℝ 2} (hu : 0 ≤ u 1)
    (hw : 0 ≤ w 1 ∧ (0 < w 1 ∨ 0 ≤ w 0)) (hu0 : u ≠ 0) (hw0 : w ≠ 0)
    (h : Complex.arg ⟨u 0, u 1⟩ < Complex.arg ⟨w 0, w 1⟩) : -- --- CONCL ---
    0 < u 0 * w 1 - u 1 * w 0 := by -- --- PROOF ---
  rw [Zonotope.cross_eq_norm_mul_sin]
  have h0 : 0 ≤ Complex.arg ⟨u 0, u 1⟩ := Complex.arg_nonneg_iff.mpr hu
  have h1 : Complex.arg (⟨w 0, w 1⟩ : ℂ) < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    rcases hw.2 with h | h
    · exact Or.inr (ne_of_gt h)
    · exact Or.inl h
  exact mul_pos (mul_pos (Zonotope.aux_norm_pos hu0) (Zonotope.aux_norm_pos hw0))
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

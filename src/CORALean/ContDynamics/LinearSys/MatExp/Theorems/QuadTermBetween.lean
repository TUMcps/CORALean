import CORALean.ContDynamics.LinearSys.MatExp.ExactSecondOrder

/-!
# The diagonal parabola stays between its two bounds

[1, Lemma 3.1], the half that says `quadTermLo`/`quadTermHi` enclose. `γ` opens
upwards, so the maximum is at an endpoint and the minimum at the vertex `-1/t`
only when the box straddles it.

Both halves come out of the two factorisations `γ x - γ a = (x - a) u` and
`γ b - γ x = (b - x) v` with `u = t + (x + a) t²/2 ≤ v = t + (x + b) t²/2`: the
sign of `v` alone decides which endpoint dominates, and `-1/t < a` is exactly
`0 ≤ t + a t²`, which is what makes `u` non-negative.

No hypothesis on `t`: at `t = 0` the `if` reads `-1/t` as `0`, which leaves the
bound sound — `γ` is then constantly `0` — and merely not tight, so the
tightness theorem is where `t ≠ 0` is paid.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `t + c t²` is `t² (c - (-1/t))`, so it takes the sign of `c` against the
vertex — and vanishes at `t = 0`, where `-1/t` reads as `0`. -/
theorem aux_vertex_sign {t c : ℝ} : t + c * t ^ 2 = t ^ 2 * (c - -1 / t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · ring
  · field_simp
    ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The parabola's value on a box never leaves `[quadTermLo, quadTermHi]`. -/
theorem MatExp.quadTerm_between {t a b x : ℝ} (h₁ : a ≤ x) (h₂ : x ≤ b) :
    MatExp.quadTermLo t a b ≤ MatExp.quadTerm t x ∧
      MatExp.quadTerm t x ≤ MatExp.quadTermHi t a b := by -- --- PROOF ---
  have hab : a ≤ b := h₁.trans h₂
  have ht2 : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
  constructor
  · -- the lower bound, by cases on whether the box straddles the vertex
    rw [MatExp.quadTermLo]
    split
    · -- `γ x + 1/2` is half a square, so `-1/2` is a floor everywhere
      have : (0:ℝ) ≤ (x * t + 1) ^ 2 := sq_nonneg _
      simp only [MatExp.quadTerm]
      nlinarith
    · rename_i hv
      -- outside the vertex, whichever endpoint the box lies past is the minimum
      rw [not_and_or, not_le, not_le] at hv
      rcases hv with hv | hv
      · -- `-1/t < a` makes `u = t + (x + a) t²/2` non-negative, so `γ a` is least
        have hu : 0 ≤ t + a * t ^ 2 := by
          rw [aux_vertex_sign]; exact mul_nonneg ht2 (by linarith)
        have hu2 : 0 ≤ t + (x + a) * t ^ 2 / 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h₁) ht2]
        have hstep := mul_nonneg (sub_nonneg.2 h₁) hu2
        refine le_trans (min_le_left _ _) ?_
        simp only [MatExp.quadTerm]
        nlinarith [hstep]
      · -- `b < -1/t` makes `v = t + (x + b) t²/2` non-positive, so `γ b` is least
        have hv' : t + b * t ^ 2 ≤ 0 := by
          rw [aux_vertex_sign]
          exact mul_nonpos_of_nonneg_of_nonpos ht2 (by linarith)
        have hv2 : t + (x + b) * t ^ 2 / 2 ≤ 0 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h₂) ht2]
        have hnb : (0:ℝ) ≤ -(t + (x + b) * t ^ 2 / 2) := by linarith
        have hstep := mul_nonneg (sub_nonneg.2 h₂) hnb
        refine le_trans (min_le_right _ _) ?_
        simp only [MatExp.quadTerm]
        nlinarith [hstep]
  · -- the upper bound: the sign of `v` says which endpoint the maximum sits at
    rw [MatExp.quadTermHi]
    rcases le_total 0 (t + (x + b) * t ^ 2 / 2) with hv | hv
    · have hstep := mul_nonneg (sub_nonneg.2 h₂) hv
      refine le_trans ?_ (le_max_right _ _)
      simp only [MatExp.quadTerm]
      nlinarith [hstep]
    · -- `u ≤ v ≤ 0` because `a ≤ b`, so the left endpoint dominates instead
      have hu : t + (x + a) * t ^ 2 / 2 ≤ 0 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hab) ht2]
      have hstep := mul_nonneg (sub_nonneg.2 h₁) (by linarith : (0:ℝ) ≤ -(t + (x + a) * t ^ 2 / 2))
      refine le_trans ?_ (le_max_left _ _)
      simp only [MatExp.quadTerm]
      nlinarith [hstep]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

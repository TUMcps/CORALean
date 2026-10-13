import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A quotient on a box lies in the hull of its corner quotients

For `n ∈ [n₁, n₂]` and `d ∈ [d₁, d₂]` with `0 < d₁`: for fixed `d`, `n / d` is monotone in `n`, and
for fixed `n`, it is monotone, in one direction or the other, in `d`, so its extremes over the box
are at corners. This is what makes the four-corner rule of `Interval.atan2` an enclosure off the
branch cut.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_div_between {k d₁ d₂ d : ℝ} (hd₁ : 0 < d₁) (hd₁' : d₁ ≤ d) (hd₂ : d ≤ d₂) :
    min (k / d₁) (k / d₂) ≤ k / d ∧ k / d ≤ max (k / d₁) (k / d₂) := by -- --- PROOF ---
  have hd : 0 < d := lt_of_lt_of_le hd₁ hd₁'
  have u1 : 1 / d ≤ 1 / d₁ := one_div_le_one_div_of_le hd₁ hd₁'
  have u2 : 1 / d₂ ≤ 1 / d := one_div_le_one_div_of_le hd hd₂
  simp only [div_eq_mul_one_div k]
  rcases le_total 0 k with h | h
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonneg_left u2 h),
      (mul_le_mul_of_nonneg_left u1 h).trans (le_max_left _ _)⟩
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonpos_left u1 h),
      (mul_le_mul_of_nonpos_left u2 h).trans (le_max_right _ _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem div_mem_corner_hull {n₁ n₂ d₁ d₂ n d : ℝ} (hd₁ : 0 < d₁) (hn₁ : n₁ ≤ n) (hn₂ : n ≤ n₂)
    (hd₁' : d₁ ≤ d) (hd₂ : d ≤ d₂) :
    min (min (n₁ / d₁) (n₁ / d₂)) (min (n₂ / d₁) (n₂ / d₂)) ≤ n / d ∧
      n / d ≤ max (max (n₁ / d₁) (n₁ / d₂)) (max (n₂ / d₁) (n₂ / d₂)) := by -- --- PROOF ---
  have hd : 0 < d := lt_of_lt_of_le hd₁ hd₁'
  have h1 : n₁ / d ≤ n / d := div_le_div_of_nonneg_right hn₁ hd.le
  have h2 : n / d ≤ n₂ / d := div_le_div_of_nonneg_right hn₂ hd.le
  obtain ⟨a1, a2⟩ := aux_div_between (k := n₁) hd₁ hd₁' hd₂
  obtain ⟨b1, b2⟩ := aux_div_between (k := n₂) hd₁ hd₁' hd₂
  constructor
  · exact (min_le_left _ _).trans (a1.trans h1)
  · exact h2.trans (b2.trans (le_max_right _ _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

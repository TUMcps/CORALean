import CORALean.ContSet.Interval.Real.Operations.Power

/-!
# `x ^ k` lies between the bounds `Interval.power` computes

The scalar fact behind `Interval.power`: for `a ≤ x ≤ b`, the power `x ^ k` lies
between `0` (even `k ≠ 0` over a box with `a < 0 < b`) or `min (a ^ k) (b ^ k)`
and `max (a ^ k) (b ^ k)`. Odd `k` is monotone; even `k` is the monotone `|x| ^ k`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.pow_between {a b x : ℝ} (k : ℕ) (h₁ : a ≤ x) (h₂ : x ≤ b) :
    (if k % 2 = 0 ∧ k ≠ 0 ∧ a < 0 ∧ 0 < b then 0 else min (a ^ k) (b ^ k)) ≤ x ^ k ∧
      x ^ k ≤ max (a ^ k) (b ^ k) := by -- --- PROOF ---
  rcases Nat.even_or_odd k with he | ho
  · -- even: `x ^ k = |x| ^ k`, monotone in `|x|`
    have hk : k % 2 = 0 := Nat.even_iff.mp he
    have hxa : x ^ k = |x| ^ k := (he.pow_abs x).symm
    have hup : x ^ k ≤ max (a ^ k) (b ^ k) := by
      rw [hxa, ← he.pow_abs a, ← he.pow_abs b]
      rcases le_total |a| |b| with h | h
      · exact le_max_of_le_right (pow_le_pow_left₀ (abs_nonneg _)
          (abs_le_max_abs_abs h₁ h₂ |>.trans (max_eq_right h).le) k)
      · exact le_max_of_le_left (pow_le_pow_left₀ (abs_nonneg _)
          (abs_le_max_abs_abs h₁ h₂ |>.trans (max_eq_left h).le) k)
    refine ⟨?_, hup⟩
    -- the lower bound: `0` in the special case, else the smaller corner power
    by_cases hs : k % 2 = 0 ∧ k ≠ 0 ∧ a < 0 ∧ 0 < b
    · rw [if_pos hs]; exact he.pow_nonneg x
    · rw [if_neg hs]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · have : 0 ≤ a ∨ b ≤ 0 := by
          by_contra hc
          push Not at hc
          exact hs ⟨hk, hk0, hc.1, hc.2⟩
        rcases this with ha | hb
        · exact min_le_of_left_le (pow_le_pow_left₀ ha h₁ k)
        · refine min_le_of_right_le ?_
          have hxb : x ≤ 0 := h₂.trans hb
          have : |b| ≤ |x| := by
            rw [abs_of_nonpos hb, abs_of_nonpos hxb]; exact neg_le_neg h₂
          rw [← he.pow_abs b, hxa]
          exact pow_le_pow_left₀ (abs_nonneg _) this k
  · -- odd: monotone, so the corners are the bounds
    have hm := ho.strictMono_pow (R := ℝ)
    have hs : ¬ (k % 2 = 0 ∧ k ≠ 0 ∧ a < 0 ∧ 0 < b) := by
      rintro ⟨h0, -⟩; exact absurd (Nat.odd_iff.mp ho) (by omega)
    rw [if_neg hs]
    exact ⟨min_le_of_left_le (hm.monotone h₁), le_max_of_le_right (hm.monotone h₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

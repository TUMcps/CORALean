module

public import CORALean.ContSet.Taylm.Real.Operations.PowBounds
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `[l, u]ᵏ` contains every power

An even power is `|t|ᵏ`, monotone in `|t|`, which is at most the larger end's magnitude and, off
an interval holding `0`, at least the smaller; an odd power is monotone.

## Inputs
* `l` – lower end
* `u` – upper end
* `t` – real point
* `k` – exponent

## Hypotheses
* `hl` – value is at least the lower end
* `hu` – value is at most the upper end

## Conclusion
* the power lies in its enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.powBounds_mem {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) (k : ℕ) : -- --- CONCL ---
    (Taylm.powBounds l u k).inf ≤ t ^ k ∧ t ^ k ≤ (Taylm.powBounds l u k).sup := by -- --- PROOF ---
  unfold Taylm.powBounds
  by_cases hk : k = 0
  · subst hk; simp
  rw [if_neg hk]
  -- a positive power, even or odd
  by_cases he : Even k
  · rw [if_pos he]
    -- an even power is `|t|ᵏ`, monotone in `|t|`
    have hupper : t ^ k ≤ max (l ^ k) (u ^ k) := by
      rw [← he.pow_abs t, ← he.pow_abs l, ← he.pow_abs u]
      -- `|t|` is at most the larger end's magnitude
      rcases le_total 0 t with ht | ht
      · exact le_max_of_le_right (pow_le_pow_left₀ (abs_nonneg _) (by
          rw [abs_of_nonneg ht]; exact le_trans hu (le_abs_self u)) _)
      · exact le_max_of_le_left (pow_le_pow_left₀ (abs_nonneg _) (by
          rw [abs_of_nonpos ht]; exact le_trans (neg_le_neg hl) (neg_le_abs l)) _)
    refine ⟨?_, hupper⟩
    split_ifs with h0
    · exact he.pow_nonneg t
    · push Not at h0
      -- both ends positive, or both negative
      rcases lt_or_ge 0 l with hl0 | hl0
      · exact min_le_of_left_le (pow_le_pow_left₀ hl0.le hl _)
      · have hu0 : u < 0 := h0 hl0
        refine min_le_of_right_le ?_
        rw [← he.pow_abs t, ← he.pow_abs u]
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          rw [abs_of_neg hu0, abs_of_neg (lt_of_le_of_lt hu hu0)]; linarith) _
  · rw [if_neg he]
    have ho : Odd k := Nat.not_even_iff_odd.1 he
    exact ⟨ho.pow_le_pow.2 hl, ho.pow_le_pow.2 hu⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.NN.Layers.Definitions.PolyDerivBound
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A fit's derivative around its centre

ℝ-only, the bracket being exact: the linear coefficient exactly, every other monomial at the
end of the box furthest from zero.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_evalPolyDeriv_sub_center_le {n : ℕ} (c : Fin (n + 1) → ℝ) {l u t : ℝ}
    (hl : l ≤ t) (hu : t ≤ u) :
    |evalPolyDeriv c t - polyDerivCenter c| ≤ polyDerivRadius c l u := by -- --- PROOF ---
  have hlm : |l| ≤ max |l| |u| := le_max_left _ _
  have hum : |u| ≤ max |l| |u| := le_max_right _ _
  -- a point of the box is no further from zero than the worse of its ends
  have htR : |t| ≤ max |l| |u| := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le l], by linarith [le_abs_self u]⟩
  have hterm : ∀ i : Fin (n + 1),
      |c i * ((i : ℕ) * t ^ ((i : ℕ) - 1)) - (if (i : ℕ) = 1 then c i else 0)|
        ≤ (if (i : ℕ) = 1 then 0 else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)) := by
    intro i
    by_cases hi : (i : ℕ) = 1
    · -- the linear term is its own coefficient, so the centre absorbs it
      rw [if_pos hi, if_pos hi, hi]
      norm_num
    · have habs : |c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))|
          = |c i| * (i : ℕ) * |t| ^ ((i : ℕ) - 1) := by
        rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
        ring
      rw [if_neg hi, if_neg hi, sub_zero, habs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) htR _)
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hsum : evalPolyDeriv c t - polyDerivCenter c
      = ∑ i : Fin (n + 1),
        (c i * ((i : ℕ) * t ^ ((i : ℕ) - 1)) - (if (i : ℕ) = 1 then c i else 0)) := by
    rw [Finset.sum_sub_distrib]
    rfl
  rw [hsum]
  show _ ≤ ∑ i : Fin (n + 1), if (i : ℕ) = 1 then 0
    else |c i| * (i : ℕ) * max |l| |u| ^ ((i : ℕ) - 1)
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => hterm i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

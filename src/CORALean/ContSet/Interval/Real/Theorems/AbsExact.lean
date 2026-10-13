module

public import CORALean.ContSet.Interval.Real.Operations.Abs

@[expose] public section

/-!
# `Interval.abs` is exactly the image under the absolute value

A point `y` of the new box is `x` or `-x` for a member `x`: the first if `y ≤ sup`, the second
otherwise, in which case `y ≤ -inf`. Needs no nonemptiness.

[1, Eq. 10], all three cases.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.abs_exact (I : Interval (Vec ℝ n)) :
    I.abs.construct = (fun x i => |x i|) '' I.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro hy
    have hy' : ∀ i, max 0 (max (I.inf i) (-I.sup i)) ≤ y i ∧
        y i ≤ max (-I.inf i) (I.sup i) := fun i => hy i
    -- the new bounds say `y` is nonnegative and no less than `inf` and `-sup`
    have hge : ∀ i, 0 ≤ y i ∧ I.inf i ≤ y i ∧ -I.sup i ≤ y i := fun i => by
      have h := (hy' i).1
      exact ⟨le_trans (le_max_left _ _) h,
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h,
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h⟩
    -- the preimage is `y` if `y ≤ sup`, and `-y` otherwise
    refine ⟨fun i => if y i ≤ I.sup i then y i else -y i, fun i => ?_, funext fun i => ?_⟩
    · show I.inf i ≤ (if y i ≤ I.sup i then y i else -y i) ∧
          (if y i ≤ I.sup i then y i else -y i) ≤ I.sup i
      by_cases h : y i ≤ I.sup i
      · rw [if_pos h]
        exact ⟨(hge i).2.1, h⟩
      · rw [if_neg h]
        have h2 : y i ≤ -I.inf i := (le_max_iff.1 (hy' i).2).resolve_right h
        exact ⟨by linarith, by linarith [(hge i).2.2]⟩
    · show |(if y i ≤ I.sup i then y i else -y i)| = y i
      by_cases h : y i ≤ I.sup i
      · rw [if_pos h, abs_of_nonneg (hge i).1]
      · rw [if_neg h, abs_neg, abs_of_nonneg (hge i).1]
  · -- the other inclusion: `|x|` between the new bounds
    rintro ⟨x, hx, rfl⟩ i
    have hx' : I.inf i ≤ x i ∧ x i ≤ I.sup i := hx i
    show max 0 (max (I.inf i) (-I.sup i)) ≤ |x i| ∧ |x i| ≤ max (-I.inf i) (I.sup i)
    refine ⟨max_le (abs_nonneg _) (max_le (le_trans hx'.1 (le_abs_self _))
      (le_trans (neg_le_neg hx'.2) (neg_le_abs _))), ?_⟩
    rw [abs_eq_max_neg]
    exact max_le (le_max_of_le_right hx'.2) (le_max_of_le_left (neg_le_neg hx'.1))


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

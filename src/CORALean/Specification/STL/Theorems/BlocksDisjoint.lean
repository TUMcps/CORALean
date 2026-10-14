module

public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# Two time blocks of length `c` do not meet

The blocks `[jc, jc + c)` of [1, Lemma 2]'s proof, one per power `j` of `X_c^j`: the different
time supports that make its `∨` distribute.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSequence.disjoint_blocks {j j' : ℕ} (h : j ≠ j') (c : ℝ≥0) :
    Disjoint (Set.Ico (j * c) (j * c + c)) (Set.Ico (j' * c) (j' * c + c)) := by -- --- PROOF ---
  -- the earlier block ends at `(j + 1) c`, which is no later than the other starts
  have key : ∀ a b : ℕ, a < b →
      Disjoint (Set.Ico (a * c) (a * c + c)) (Set.Ico (b * c) (b * c + c)) := by
    intro a b hab
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have : ((a + 1 : ℕ) : ℝ≥0) * c ≤ b * c := by
      gcongr
      exact_mod_cast hab
    push_cast at this
    rw [add_mul, one_mul] at this
    exact absurd (lt_of_lt_of_le hx.2 this) (not_lt.2 hx'.1)
  rcases lt_or_gt_of_ne h with h | h
  · exact key j j' h
  · exact (key j' j h).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

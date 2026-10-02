import CORALean.NN.Definitions.MergeBucket
import Mathlib.Tactic.Positivity

/-!
# A large enough tolerance takes every neuron

[1]'s Alg. 1 search's other endpoint: together with `mergeBucket_card_mono`,
this is what makes a binary search on `δ` well posed — the quantity it moves is
monotone, and its range reaches the top, so any rate between "merge nothing"
and "merge everything" is bracketed. Which `δ` the search settles on still
owes no proof; the merge is sound at every bucket regardless, the same
separation `ConPolyZono.reduceBy_outer` keeps at every partition.

Not claimed: that every rate `ρ` is hit *exactly*. A bucket's index count is
an integer that jumps as `δ` grows, so a rate strictly between two adjacent
counts is unreachable by any `δ`.

The witness sums nonnegative terms rather than reaching for `Finset.sup'`,
which needs `Fin n` nonempty — this statement holds, vacuously but usefully,
at `n = 0` too. Same trick as `exists_mergeTolerance`'s `1 + ∑ …` denominator.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- At a tolerance wide enough — the sum, over every neuron, of its distance to `y` on both
sides — every neuron is in the bucket. -/
theorem exists_mergeBucket_all {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y : ℝ) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ i, mergeBucket Y y δ i := by -- --- PROOF ---
  refine ⟨∑ i, (|y - Y.inf i| + |Y.sup i - y|), Finset.sum_nonneg fun i _ => by positivity, ?_⟩
  intro i
  -- this index's own two terms are at most the sum taken over every index
  have hle : |y - Y.inf i| + |Y.sup i - y| ≤ ∑ j, (|y - Y.inf j| + |Y.sup j - y|) :=
    Finset.single_le_sum (f := fun j => |y - Y.inf j| + |Y.sup j - y|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  exact ⟨by linarith [le_abs_self (y - Y.inf i), abs_nonneg (Y.sup i - y)],
    by linarith [le_abs_self (Y.sup i - y), abs_nonneg (y - Y.inf i)]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Real.Operations.RdivideNumeratorCora

@[expose] public section

/-!
# CORA's `c ./ I` drops half the range for `c < 0` and `sup(I) = 0`

`-1 ./ interval(-2, 0)` is `[-Inf, 0.5]` in CORA (`@interval/rdivide.m` l. 86-88), while `-1/x`
on `[-2, 0)` takes the values `[0.5, +Inf)`: at `x = -1/2` it is `2`. The public `./` of a numeric
and an interval operand dispatches there, and a scalar passes `size(numerator) == 1`. Read from
the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `c < 0` and `lo < 0`, the value at `lo / 2 ∈ [lo, 0)` lies above CORA's upper bound
`c / lo` of `c ./ interval(lo, 0)`; `c = -1`, `lo = -2` is the witness. -/
theorem Interval.rdivideNumeratorCora_counterexample {c lo : ℝ} (hc : c < 0) (hlo : lo < 0) :
    lo ≤ lo / 2 ∧ lo / 2 < 0 ∧
      (Interval.rdivideNumeratorCora c lo 0).sup <
        ((c / (lo / 2) : ℝ) : EReal) := by -- --- PROOF ---
  refine ⟨by linarith, by linarith, ?_⟩
  -- the branch `sup == 0` is taken: `lo < 0`, `hi = 0`
  have h : ¬ (lo < 0 ∧ 0 < (0 : ℝ)) := fun h => lt_irrefl _ h.2
  simp only [Interval.rdivideNumeratorCora, h, if_false, if_true]
  rw [EReal.coe_lt_coe_iff]
  -- `c / (lo / 2) = 2 (c / lo)` and `c / lo > 0`
  have h2 : c / (lo / 2) = 2 * (c / lo) := by field_simp
  have h3 : 0 < c / lo := div_pos_of_neg_of_neg hc hlo
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `Interval.rdivideNumeratorCora`: `c ./ I` as CORA's code computes it

`@interval/rdivide.m`, a scalar numerator over an interval (l. 84-100; the same-size matrix
branch, l. 103-119, is the same entrywise):

```
res.inf = min(numerator ./ denominator.sup, numerator ./ denominator.inf);
res.sup = max(numerator ./ denominator.sup, numerator ./ denominator.inf);
ind1 = denominator.sup == 0;
res.inf(ind1) = -Inf;  res.sup(ind1) = numerator ./ denominator.inf(ind1);
ind1 = denominator.inf < 0 & denominator.sup > 0;
res.inf(ind1) = -Inf;  res.sup(ind1) = +Inf;
```

The `sup == 0` branch is right for `c > 0` only. One dimension, `±Inf` as `EReal`. Not modelled:
`inf = 0` (MATLAB's `c/0 = ±Inf`; in `ℝ` it is `0`). Read from the source, not run.

# CORA's `c ./ I` drops half the range for `c < 0` and `sup(I) = 0`

`-1 ./ interval(-2, 0)` is `[-Inf, 0.5]` in CORA (`@interval/rdivide.m` l. 86-88), while `-1/x`
on `[-2, 0)` takes the values `[0.5, +Inf)`: at `x = -1/2` it is `2`. The public `./` dispatches
there, a scalar passing `size(numerator) == 1`. Read from the source, not run.

## Inputs
* `c` – negative numerator
* `lo` – negative lower bound

## Hypotheses
* `hc` – numerator negative
* `hlo` – lower bound negative

## Conclusion
* CORA's upper bound lies below the true quotient
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `c ./ interval(lo, hi)`, one dimension. -/
noncomputable def Interval.rdivideNumeratorCora (c lo hi : ℝ) : Interval EReal :=
  -- inf < 0 & sup > 0
  if lo < 0 ∧ 0 < hi then ⟨⊥, ⊤⟩
  -- sup == 0
  else if hi = 0 then ⟨⊥, ((c / lo : ℝ) : EReal)⟩
  -- min / max of `c ./ sup` and `c ./ inf`
  else ⟨((min (c / hi) (c / lo) : ℝ) : EReal), ((max (c / hi) (c / lo) : ℝ) : EReal)⟩


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

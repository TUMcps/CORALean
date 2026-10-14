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
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `res` for `c ./ interval(lo, hi)`, one dimension. -/
noncomputable def Interval.rdivideNumeratorCora (c lo hi : ℝ) : Interval EReal :=
  -- inf < 0 & sup > 0
  if lo < 0 ∧ 0 < hi then ⟨⊥, ⊤⟩
  -- sup == 0
  else if hi = 0 then ⟨⊥, ((c / lo : ℝ) : EReal)⟩
  -- min / max of `c ./ sup` and `c ./ inf`
  else ⟨((min (c / hi) (c / lo) : ℝ) : EReal), ((max (c / hi) (c / lo) : ℝ) : EReal)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Interval.randPointIntervalMatrixCora`: `randPoint` of an interval matrix as CORA's code samples

`@intervalMatrix/randPoint.m` (l. 46-53) takes the entrywise half-width `rad` as the width:

```
c  = center(intMat.int);   lb = infimum(intMat.int);   r = rad(intMat);   % r = 0.5*(sup - inf)
'extreme':   M = c + 0.5*sign(2*rand([n,N])-1) .* r;
'standard':  M = lb + rand([n,N]) .* r;
```

One entry `[lo, hi]` with `r = (hi - lo)/2` and the random draw `u ∈ [0, 1)`, `s = ±1` the sign.
Read from the source, not run.

# CORA's `randPoint` of an interval matrix covers half of each entry and never the vertices

For `intervalMatrix(0, 1)`, the entry `[-1, 1]`: `'standard'` returns `-1 + u * 1 ∈ [-1, 0)`, the
lower half, and `'extreme'` returns `±1/2`, no vertex. The containment tests pass, as every sample
is inside the box.

## Inputs
* `lo` – lower bound
* `hi` – upper bound

## Hypotheses
* `h` – bounds strictly ordered

## Conclusion
* CORA's sampling stays below the midpoint and never reaches either end
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `'standard'` sample of the entry `[lo, hi]` for the draw `u`. -/
noncomputable def Interval.randPointStandardIntervalMatrixCora (lo hi u : ℝ) : ℝ :=
  -- lb + rand .* r
  lo + u * ((hi - lo) / 2)

/-- CORA's `'extreme'` sample of the entry `[lo, hi]` for the sign `s`. -/
noncomputable def Interval.randPointExtremeIntervalMatrixCora (lo hi s : ℝ) : ℝ :=
  -- c + 0.5*sign(..) .* r
  (lo + hi) / 2 + (1 / 2) * s * ((hi - lo) / 2)


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a non-degenerate entry, no `'standard'` draw `u ∈ [0, 1]` exceeds the center, and an
`'extreme'` draw with `s = ±1` is neither endpoint. -/
theorem Interval.randPointIntervalMatrix_cora_counterexample {lo hi : ℝ}
    (h : lo < hi) : -- --- CONCL ---
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      Interval.randPointStandardIntervalMatrixCora lo hi u ≤ (lo + hi) / 2) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) →
      Interval.randPointExtremeIntervalMatrixCora lo hi s ≠ lo ∧
      Interval.randPointExtremeIntervalMatrixCora lo hi s ≠ hi) := by -- --- PROOF ---
  refine ⟨fun u _ hu1 => ?_, fun s hs => ?_⟩
  · unfold Interval.randPointStandardIntervalMatrixCora
    nlinarith
  · unfold Interval.randPointExtremeIntervalMatrixCora
    rcases hs with rfl | rfl <;> constructor <;> intro h' <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

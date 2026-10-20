module

public import CORALean.Specification.PointSegmentSignal.Operations.TimeOrInf
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The loop of the point-wise combination

The `while` loop of `pointSegmentSignal.combine` for one output. Each pass takes the smallest
unconsumed time among the inputs, evaluates `op` at the point and on the interval after it, and
appends the point unless it repeats the interval before and after. CORA's `eps` tie tolerance
becomes equality; the passes are bounded by `fuel` (the total number of time points suffices).

## Inputs
* `T` – time type
* `ι` – index type of the inputs
* `op` – pointwise operator on Boolean values
* `sig` – input signals

## Output
* the time points and values of one combined output
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `while any(inIdx <= cellfun(@length,varargin))` loop, output arrays `tp` and `val`. -/
def PointSegmentSignal.combineLoop {T : Type} [LinearOrder T] [Zero T] {ι : Type} [Fintype ι]
    (op : (ι → Bool) → Bool) (sig : ι → PointSegmentSignal T) :
    ℕ → (ι → ℕ) → List T → List Bool → List T × List Bool
  | 0, _, tp, val => (tp, val)
  | fuel + 1, inIdx, tp, val =>
    if ∃ k, inIdx k ≤ (sig k).length then
      -- 1. times = arrayfun(@aux_time,varargin,inIdx); timePoint = min(times)
      let times := fun k => (sig k).timeOrInf (inIdx k)
      let timePoint := Finset.univ.inf times
      -- 2. isMin = times - timePoint < eps
      let isMin := fun k => decide (times k = timePoint)
      -- 3. pointValues = op(...); intValues = op(...)
      let pointValue := op fun k =>
        if isMin k then (sig k).pointValue (inIdx k) else (sig k).precIntervalValue (inIdx k)
      let intValue := op fun k =>
        if isMin k then (sig k).succIntervalValue (inIdx k) else (sig k).precIntervalValue (inIdx k)
      -- 4. inIdx(minIdx) = inIdx(minIdx) + 1
      let inIdx' := fun k => if isMin k then inIdx k + 1 else inIdx k
      -- 5. skip a point equal to the preceding and the following interval
      if tp ≠ [] ∧ pointValue = val.getD (val.length - 1) false ∧ pointValue = intValue then
        PointSegmentSignal.combineLoop op sig fuel inIdx' tp val
      else
        PointSegmentSignal.combineLoop op sig fuel inIdx' (tp ++ [timePoint.untopD 0])
          (val ++ [pointValue, intValue])
    else (tp, val)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

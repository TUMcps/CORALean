module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellRel
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import Mathlib.Order.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# A run of values is an interval of times

The times between the lower end of value `r` and the upper end of value `f` (one-based, as
`precTimeAtValIdx` and `succTimeAtValIdx` take them) are those whose `cell` is among `r - 1, ..., f
- 1`.

## Inputs
* `T` – time type
* `s` – signal
* `r` – first value index
* `f` – last value index
* `t` – time

## Hypotheses
* `hs` – the signal is valid
* `hr` – the first index is positive
* `hrN` – the first index is in range
* `hf` – the last index is positive
* `hfN` – the last index is in range
* `ht` – the time is nonnegative

## Conclusion
* a time lies in the interval iff its cell is in the run
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `stlInterval(lb,ub,lc,rc)` of values `r` to `f` holds the times with `cell` in that run. -/
theorem PointSegmentSignal.cell_mem_bounds {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (r f : ℕ) (hr : 1 ≤ r) (hrN : r ≤ s.values.length)
    (hf : 1 ≤ f) (hfN : f ≤ s.values.length) (t : T) (ht : 0 ≤ t) : -- --- CONCL ---
    STLInterval.IsInBounds (s.precTimeAtValIdx r).1 (s.succTimeAtValIdx f).1
      (s.precTimeAtValIdx r).2 (s.succTimeAtValIdx f).2 t ↔
      r - 1 ≤ s.cell t ∧ s.cell t ≤ f - 1 := by -- --- PROOF ---
  have h1 := s.cell_ge_iff hs t ht (r - 1) (by omega)
  have h2 := s.cell_le_iff hs t ht (f - 1) (by omega)
  rw [show r - 1 + 1 = r by omega] at h1
  rw [show f - 1 + 1 = f by omega] at h2
  rw [STLInterval.IsInBounds, h1, h2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

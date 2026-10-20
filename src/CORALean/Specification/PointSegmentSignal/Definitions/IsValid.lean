module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Basic

@[expose] public section

/-!
# What the constructor accepts

The checks of `pointSegmentSignal.m`'s `aux_checkInputs`: non-empty arrays, two values per time
point, first time point `0`, strictly increasing times, and no point whose value matches both its
preceding and following interval (so a signal has one representation).

## Inputs
* `T` – time type
* `s` – signal

## Output
* the constructor's input checks pass
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_checkInputs(timePoints,values)` passes. -/
def PointSegmentSignal.IsValid {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T) :
    Prop :=
  s.timePoints ≠ [] ∧ s.values.length = 2 * s.timePoints.length ∧ s.timePoints.head? = some 0 ∧
    s.timePoints.Pairwise (· < ·) ∧
    ∀ i, 1 ≤ i → i < s.timePoints.length →
      ¬ (s.values.getD (2 * i) false = s.values.getD (2 * i + 1) false ∧
         s.values.getD (2 * i) false = s.values.getD (2 * i - 1) false)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

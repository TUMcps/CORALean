module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# `PointSegmentSignal/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ===============================  `PointSegmentSignal.length`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `l = length(obj)`: the number of time points. -/
def PointSegmentSignal.length {T : Type} (s : PointSegmentSignal T) : ℕ := s.timePoints.length


-- =================================  `PointSegmentSignal.not`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~obj`: the same time points, every value negated. -/
def PointSegmentSignal.not {T : Type} (s : PointSegmentSignal T) : PointSegmentSignal T :=
  ⟨s.timePoints, s.values.map (!·)⟩


-- =============================  `PointSegmentSignal.pointValue`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `pointValue(obj,i)`, `i` counted from `1`: the value at the `i`-th time point. -/
def PointSegmentSignal.pointValue {T : Type} (s : PointSegmentSignal T) (i : ℕ) : Bool :=
  s.values.getD (2 * i - 2) false


-- ==========================  `PointSegmentSignal.precIntervalValue`  ========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `precIntervalValue(obj,i)`: the value on the interval before the `i`-th time point. -/
def PointSegmentSignal.precIntervalValue {T : Type} (s : PointSegmentSignal T) (i : ℕ) : Bool :=
  s.values.getD (2 * i - 3) false


-- ==========================  `PointSegmentSignal.succIntervalValue`  ========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `succIntervalValue(obj,i)`: the value on the interval after the `i`-th time point. -/
def PointSegmentSignal.succIntervalValue {T : Type} (s : PointSegmentSignal T) (i : ℕ) : Bool :=
  s.values.getD (2 * i - 1) false


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

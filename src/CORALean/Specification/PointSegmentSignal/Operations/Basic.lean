module

public import CORALean.Global.Interfaces
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


-- ====================================  `List.matlabDiff`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- `diff(x)` of a logical array: the differences of neighbours, `-1`, `0` or `1`. -/
def List.matlabDiff (l : List Bool) : List ℤ :=
  List.zipWith (fun a b => (b.toNat : ℤ) - a.toNat) l l.tail


-- ====================================  `List.matlabFind`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `find(x)` with a predicate: the one-based indices of the entries that satisfy it. -/
def List.matlabFind {α : Type} (p : α → Bool) (l : List α) : List ℕ :=
  (List.range' 1 l.length).filter (fun j => (l[j - 1]?).any p)


-- =================================  `PointSegmentSignal.eq`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj == other`: the time points agree (`withinTol` with `eps` in CORA, `TimeOrder.Eqv` here)
and the values are equal. -/
def PointSegmentSignal.eq {T : Type} [TimeOrder T] (a b : PointSegmentSignal T) : Bool :=
  a.timePoints.isEqv b.timePoints (fun x y => decide (TimeOrder.Eqv x y)) && a.values == b.values


-- ===============================  `PointSegmentSignal.length`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `l = length(obj)`: the number of time points. -/
def PointSegmentSignal.length {T : Type} (s : PointSegmentSignal T) : ℕ := s.timePoints.length


-- ===============================  `PointSegmentSignal.mapTime`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The signal with every time point mapped by `f`, as a float signal is read by `toReal`. -/
def PointSegmentSignal.mapTime {T T' : Type} (f : T → T') (s : PointSegmentSignal T) :
    PointSegmentSignal T' :=
  ⟨s.timePoints.map f, s.values⟩


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


-- ==========================  `PointSegmentSignal.precTimeAtValIdx`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `[time,atPoint] = precTimeAtValIdx(obj,i)`: the time point before the `i`-th stored value. -/
def PointSegmentSignal.precTimeAtValIdx {T : Type} [Zero T] (s : PointSegmentSignal T) (i : ℕ) :
    T × Bool :=
  (s.timePoints.getD ((i + 1) / 2 - 1) 0, decide (i % 2 = 1))


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

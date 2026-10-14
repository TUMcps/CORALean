module

public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Definitions.ContainsPoint
public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Operations.And
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Minus
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.Supremum

@[expose] public section

/-!
# The until of two lists of intervals

`out = aux_intervalUntil(lhsInt,untilInt,rhsInt)` of `pointSegmentSignal/until.m`: the signal that
is `true` at the times `t` for which an interval of `lhsInt`, closed at the left, reaches an
interval of `rhsInt`, closed at the right, at a time `t'` with `t' - t` in the until interval, minus
zero; and, if the until interval contains `0`, at the times of `rhsInt`. `contains(0)` and
`representsa` are taken at tolerance `0`; CORA's default tolerance of `contains` is a few `eps`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `out = aux_intervalUntil(lhsInt,untilInt,rhsInt)`. -/
noncomputable def PointSegmentSignal.intervalUntil (lhsInt : List STLInterval)
    (untilInt : STLInterval) (rhsInt : List STLInterval) : PointSegmentSignal ℝ :=
  -- 1. out = pointSegmentSignal.indicator(stlInterval(0,inf),false,false)
  let out := PointSegmentSignal.indicator (STLInterval.stlInterval 0 ⊤ true true) false false
  -- 2. untilIntNoZero: if untilInt.contains(0), the interval `(0,ub]` or `(0,ub)` of its supremum
  let untilIntNoZero := if untilInt.containsPoint 0 0 then
    STLInterval.stlInterval 0 (untilInt.supremum.value.getD 0) false untilInt.supremum.closed
    else untilInt
  -- 3. for each pair, the times `t` with a witness `t'`: set them to true unless there are none
  let out := lhsInt.foldl (fun out lhs => rhsInt.foldl (fun out rhs =>
    let posShift := ((rhs.and_ lhs.rightClosure).minus untilIntNoZero).and_ lhs.leftClosure
    if posShift.representsa_ 0 .emptySet then out else out.set posShift true) out) out
  -- 4. if untilInt.contains(0), the right-hand side holding at `t` itself is a witness
  if untilInt.containsPoint 0 0 then rhsInt.foldl (fun out rhs => out.set rhs true) out else out

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

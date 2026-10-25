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
interval of `rhsInt`, closed at the right, at a `t'` with `t' - t` in the until interval, minus
zero; and, if that interval contains `0`, at the times of `rhsInt`. `contains(0)` and `representsa`
use tolerance `0`. With one interval on each side this is the unitary until of [1, Eq. 1].
Refinement pending: CORA computes this in doubles, its refinement over `𝕋` is not yet written.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
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
noncomputable def PointSegmentSignal.intervalUntil (lhsInt : List (STLInterval ℝ))
    (untilInt : STLInterval ℝ) (rhsInt : List (STLInterval ℝ)) : PointSegmentSignal ℝ :=
  -- 1. out = pointSegmentSignal.indicator(stlInterval(0,inf),false,false)
  let out := PointSegmentSignal.indicator (STLInterval.stlInterval (0 : ℝ) ⊤ true true (by simp))
    false false
  -- 2. untilIntNoZero: if untilInt.contains(0), the interval `(0,ub]` or `(0,ub)` of its supremum
  let untilIntNoZero := if untilInt.containsPoint 0 0 then
    STLInterval.stlInterval (0 : ℝ) (untilInt.supremum.value.getD 0) false
      untilInt.supremum.closed (by simp)
    else untilInt
  -- 3. for each pair, the times `t` with a witness `t'`: set them to true unless there are none
  let out := lhsInt.foldl (fun out lhs => rhsInt.foldl (fun out rhs =>
    let posShift := ((rhs.and_ lhs.rightClosure).minus untilIntNoZero).and_ lhs.leftClosure
    if posShift.representsa_ 0 .emptySet then out else out.set posShift true) out) out
  -- 4. if untilInt.contains(0), the right-hand side holding at `t` itself is a witness
  if untilInt.containsPoint 0 0 then rhsInt.foldl (fun out rhs => out.set rhs true) out else out

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

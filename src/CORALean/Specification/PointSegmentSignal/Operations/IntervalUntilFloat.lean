module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Operations.And
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.Supremum

@[expose] public section

/-!
# The until of two lists of intervals over a float scalar

`aux_intervalUntil` of `pointSegmentSignal/until.m` with time stamps in `𝕋`, as
`intervalUntil`, with the time shift `(rhs & lhs.rightClosure) - untilIntNoZero` done by `shift`:
`minusInward` gives a signal true only where the exact one is (`intervalUntilFloat_inner`),
`minus` one true wherever it is (`intervalUntilFloat_outer`). `contains(0)` and `representsa`
at tolerance `0` are tests on the stored bounds, compared exactly.

## Inputs
* `shift` – the difference of two time intervals
* `lhsInt` – intervals of the left signal
* `untilInt` – until interval
* `rhsInt` – intervals of the right signal

## Output
* the until signal of the intervals
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `untilInt.contains(0)` at tolerance `0`: the lower end is a closed `0`. -/
def PointSegmentSignal.aux_containsZero : STLInterval 𝕋 → Bool
  | .empty => false
  | .nonempty l _ lc _ _ _ _ => lc && decide (toReal l = toReal (0 : 𝕋))

/-- `untilIntNoZero`: the until interval without `0`, `(0,ub]` or `(0,ub)` if it contains `0`. -/
def PointSegmentSignal.aux_untilIntNoZero (untilInt : STLInterval 𝕋) : STLInterval 𝕋 :=
  if PointSegmentSignal.aux_containsZero untilInt then
    STLInterval.stlInterval 0 (untilInt.supremum.value.getD 0) false untilInt.supremum.closed
      toReal_zero_eq.ge
  else untilInt


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = aux_intervalUntil(lhsInt,untilInt,rhsInt)` with the time shift `shift`. -/
def PointSegmentSignal.intervalUntilFloat (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (lhsInt : List (STLInterval 𝕋)) (untilInt : STLInterval 𝕋) (rhsInt : List (STLInterval 𝕋)) :
    PointSegmentSignal 𝕋 :=
  -- 1. out = pointSegmentSignal.indicator(stlInterval(0,inf),false,false)
  let out := PointSegmentSignal.indicator
    (STLInterval.stlInterval (0 : 𝕋) ⊤ true true toReal_zero_eq.ge) false false
  -- 2. untilIntNoZero: if untilInt.contains(0), the interval `(0,ub]` or `(0,ub)` of its supremum
  let untilIntNoZero := PointSegmentSignal.aux_untilIntNoZero untilInt
  -- 3. for each pair, the times `t` with a witness `t'`: set them to true unless there are none
  let out := lhsInt.foldl (fun out lhs => rhsInt.foldl (fun out rhs =>
    let posShift := (shift (rhs.and_ lhs.rightClosure) untilIntNoZero).and_ lhs.leftClosure
    match posShift with
    | .empty => out
    | .nonempty .. => out.set posShift true) out) out
  -- 4. if untilInt.contains(0), the right-hand side holding at `t` itself is a witness
  if PointSegmentSignal.aux_containsZero untilInt then
    rhsInt.foldl (fun out rhs => out.set rhs true) out
  else out

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

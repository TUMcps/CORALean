module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.At

@[expose] public section

/-!
# Tentative Kleene signals

CORA's `tentativeKleeneSignal` (`specification/signals/tentativeKleeneSignal.m`): what an
observation of a signal leaves possible, stored as two Boolean `pointSegmentSignal`s, `canBeTrue`
and `canBeFalse`. A time where only the first holds is `True`, only the second `False`, both
`Unknown`, neither `Inconclusive` (nothing observed there yet). The constructor checks nothing;
`IsValid` asks both parts to be valid signals, and `TentativeKleeneSignal.at` is the value they
denote.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure TentativeKleeneSignal (T : Type) where
  canBeTrue : PointSegmentSignal T
  canBeFalse : PointSegmentSignal T
  deriving DecidableEq

/-- Both parts are valid signals. -/
def TentativeKleeneSignal.IsValid {T : Type} [LinearOrder T] [Zero T]
    (s : TentativeKleeneSignal T) : Prop :=
  s.canBeTrue.IsValid ∧ s.canBeFalse.IsValid

/-- The value at a time: `Inconclusive` if neither value can be, `Unknown` if both can. -/
def TentativeKleeneSignal.at {T : Type} [LinearOrder T] (s : TentativeKleeneSignal T) (time : T) :
    FourValued :=
  match s.canBeTrue.at time, s.canBeFalse.at time with
  | true, true => .uu
  | true, false => .tt
  | false, true => .ff
  | false, false => .ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.PointSegmentSignal.Operations.AnyTrue
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# `KleeneSignal/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ====================================  `KleeneSignal.at`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj.at(time)`: `Unknown` where `isUnknown` holds, else the Boolean part. -/
def KleeneSignal.at {T : Type} [LinearOrder T] (s : KleeneSignal T) (time : T) : Kleene :=
  if s.isUnknown.at time then Kleene.uu else Kleene.fromBool (s.signal.at time)


-- ====================================  `KleeneSignal.eq`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj == other`: both parts are equal (structurally). -/
def KleeneSignal.eq {T : Type} [LinearOrder T] (a b : KleeneSignal T) : Bool :=
  if a.signal = b.signal ∧ a.isUnknown = b.isUnknown then true else false


-- =================================  `KleeneSignal.indicator`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleeneSignal.indicator(interval,val,default)`: both parts are indicators. -/
noncomputable def KleeneSignal.indicator (I : STLInterval) (val default : Kleene) :
    KleeneSignal ℝ :=
  ⟨PointSegmentSignal.indicator I val.toBool default.toBool,
    PointSegmentSignal.indicator I val.isUnknown default.isUnknown⟩


-- ==============================  `KleeneSignal.fromBoolSignal`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleeneSignal.fromBoolSignal(bSig)`: a Boolean signal with nothing unknown. -/
noncomputable def KleeneSignal.fromBoolSignal (bSig : PointSegmentSignal ℝ) : KleeneSignal ℝ :=
  ⟨bSig, PointSegmentSignal.indicator STLInterval.empty false false⟩


-- ====================================  `KleeneSignal.not`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~obj`: the Boolean part is negated, the unknown part kept. -/
def KleeneSignal.not {T : Type} (s : KleeneSignal T) : KleeneSignal T :=
  ⟨s.signal.not, s.isUnknown⟩


-- ====================================  `KleeneSignal.set`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sig = set(obj,interval,value)`: both parts are set on the interval. -/
noncomputable def KleeneSignal.set (s : KleeneSignal ℝ) (I : STLInterval) (value : Kleene) :
    KleeneSignal ℝ :=
  ⟨s.signal.set I value.toBool, s.isUnknown.set I value.isUnknown⟩


-- ===============================  `KleeneSignal.toBoolSignal?`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toBoolSignal(obj)` without argument; CORA throws if some value is unknown, here `none`. -/
def KleeneSignal.toBoolSignal? {T : Type} [LinearOrder T] [Zero T] (s : KleeneSignal T) :
    Option (PointSegmentSignal T) :=
  if s.isUnknown.anyTrue 0 ⊤ true false id then none else some s.signal


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

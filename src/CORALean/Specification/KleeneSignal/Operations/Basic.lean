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

`IsRefinedBy` is `λ ≺ Λ` of [1, Sec. 4.2 (refinements)]: the Boolean signal takes the value of the
three-valued one wherever that is not unknown.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [TimeOrder 𝕋]


-- ====================================  `KleeneSignal.at`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj.at(time)`: `Unknown` where `isUnknown` holds, else the Boolean part. -/
def KleeneSignal.at {T : Type} [TimeOrder T] (s : KleeneSignal T) (time : T) : Kleene :=
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
def KleeneSignal.indicator (I : STLInterval 𝕋) (val default : Kleene) : KleeneSignal 𝕋 :=
  ⟨PointSegmentSignal.indicator I val.toBool default.toBool,
    PointSegmentSignal.indicator I val.isUnknown default.isUnknown⟩


-- ==============================  `KleeneSignal.fromBoolSignal`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `kleeneSignal.fromBoolSignal(bSig)`: a Boolean signal with nothing unknown. -/
def KleeneSignal.fromBoolSignal (bSig : PointSegmentSignal 𝕋) : KleeneSignal 𝕋 :=
  ⟨bSig, PointSegmentSignal.indicator STLInterval.empty false false⟩


-- ================================  `KleeneSignal.IsRefinedBy`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `λ ≺ Λ`, [1, Sec. 4.2 (refinements)]: the Boolean signal refines `s` if at every time `t ≥ 0`
it takes the value of `s` wherever that is not `Unknown`. -/
def KleeneSignal.IsRefinedBy (s : KleeneSignal ℝ) (l : PointSegmentSignal ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (s.at t).IsRefinedBy (l.at t)


-- ==================================  `KleeneSignal.mapTime`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The signal with every time point of both parts mapped by `f`, as a float signal is read by
`toReal`. -/
def KleeneSignal.mapTime {T T' : Type} (f : T → T') (s : KleeneSignal T) : KleeneSignal T' :=
  ⟨s.signal.mapTime f, s.isUnknown.mapTime f⟩


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
def KleeneSignal.set (s : KleeneSignal 𝕋) (I : STLInterval 𝕋) (value : Kleene) :
    KleeneSignal 𝕋 :=
  ⟨s.signal.set I value.toBool, s.isUnknown.set I value.isUnknown⟩


-- ===============================  `KleeneSignal.toBoolSignal?`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toBoolSignal(obj)` without argument; CORA throws if some value is unknown, here `none`. -/
def KleeneSignal.toBoolSignal? {T : Type} [TimeOrder T] [Zero T] (s : KleeneSignal T) :
    Option (PointSegmentSignal T) :=
  if s.isUnknown.anyTrue 0 ⊤ true false id then none else some s.signal


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

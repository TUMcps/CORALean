module

public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.FourValuedSignal.FourValuedSignal
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# `FourValuedSignal/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

`IsRefinedBy` is `Λ ≺ Λ̃` of [1, Sec. 4.3 (refinements)]: the Kleene signal takes the value of the
four-valued one wherever that is not inconclusive.
Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ==================================  `FourValuedSignal.at`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj.at(time)`: `Inconclusive` where `isInconclusive` holds, else the Kleene part. -/
def FourValuedSignal.at {T : Type} [LinearOrder T] (s : FourValuedSignal T) (time : T) :
    FourValued :=
  if s.isInconclusive.at time then FourValued.ii else FourValued.fromKleene (s.signal.at time)


-- ==================================  `FourValuedSignal.eq`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `obj == other`: both parts are equal (structurally). -/
def FourValuedSignal.eq {T : Type} [LinearOrder T] (a b : FourValuedSignal T) : Bool :=
  if a.signal.eq b.signal = true ∧ a.isInconclusive = b.isInconclusive then true else false


-- ===============================  `FourValuedSignal.indicator`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fourValuedSignal.indicator(interval,val,default)`: both parts are indicators. -/
noncomputable def FourValuedSignal.indicator (I : STLInterval) (val default : FourValued) :
    FourValuedSignal ℝ :=
  ⟨KleeneSignal.indicator I val.toKleene default.toKleene,
    PointSegmentSignal.indicator I val.isInconclusive default.isInconclusive⟩


-- ===========================  `FourValuedSignal.fromKleeneSignal`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fourValuedSignal.fromKleeneSignal(kSig)`: a Kleene signal with nothing inconclusive. -/
noncomputable def FourValuedSignal.fromKleeneSignal (kSig : KleeneSignal ℝ) : FourValuedSignal ℝ :=
  ⟨kSig, PointSegmentSignal.indicator STLInterval.empty false false⟩


-- ==============================  `FourValuedSignal.IsRefinedBy`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Λ ≺ Λ̃`, [1, Sec. 4.3 (refinements)]: the Kleene signal refines `s` if at every time `t ≥ 0`
it takes the value of `s` wherever that is not `Inconclusive`. -/
def FourValuedSignal.IsRefinedBy (s : FourValuedSignal ℝ) (k : KleeneSignal ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (s.at t).IsRefinedBy (k.at t)


-- ==================================  `FourValuedSignal.not`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~obj`: the Kleene part is negated, the inconclusive part kept. -/
def FourValuedSignal.not {T : Type} (s : FourValuedSignal T) : FourValuedSignal T :=
  ⟨s.signal.not, s.isInconclusive⟩


-- ==================================  `FourValuedSignal.set`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sig = set(obj,interval,value)`: both parts are set on the interval. -/
noncomputable def FourValuedSignal.set (s : FourValuedSignal ℝ) (I : STLInterval) (value :
    FourValued) :
    FourValuedSignal ℝ :=
  ⟨s.signal.set I value.toKleene, s.isInconclusive.set I value.isInconclusive⟩


-- ============================  `FourValuedSignal.toKleeneSignal?`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `toKleeneSignal(obj)` without argument; CORA throws if a value is inconclusive, here `none`. -/
def FourValuedSignal.toKleeneSignal? {T : Type} [LinearOrder T] [Zero T]
    (s : FourValuedSignal T) : Option (KleeneSignal T) :=
  if s.isInconclusive.anyTrue 0 ⊤ true false id then none else some s.signal


-- =============================  `FourValuedSignal.uniformSignal`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fourValuedSignal.uniformSignal(val)`: the constant signal. -/
noncomputable def FourValuedSignal.uniformSignal (val : FourValued) : FourValuedSignal ℝ :=
  FourValuedSignal.indicator STLInterval.empty val val


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

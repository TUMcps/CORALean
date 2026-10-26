module

public import CORALean.Specification.FourValuedSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime
public import CORALean.Specification.STLInterval.Operations.ToLeft
public import CORALean.Specification.STLInterval.Operations.ToRight
public import CORALean.Specification.STLInterval.Theorems.StlIntervalToRealInterval
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.GetInterval
public import CORALean.Specification.TentativeKleeneSignal.Operations.ToFourValued

@[expose] public section

/-!
# The signal on an interval at a float time type, read as reals

Over a float scalar `𝕋` the times left and right of the interval are built by the constructor
on the reals the bounds denote, ruled out and the result made four-valued, all exactly, so the
float signal read as reals is the one of the interval the float one denotes.

## Inputs
* `s` – signal
* `I` – time interval

## Hypotheses
* none

## Conclusion
* it commutes with reading the time points as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The times left of a float interval, read as reals, are those left of the interval it denotes. -/
private theorem STLInterval.aux_toLeft_toRealInterval (I : STLInterval 𝕋) : -- --- CONCL ---
    I.toLeft.map STLInterval.toRealInterval = I.toRealInterval.toLeft := by -- --- PROOF ---
  cases I with
  | empty => rfl
  | nonempty l u lc rc _ _ _ =>
    simp only [STLInterval.toLeft, Option.map_some, STLInterval.stlInterval_toRealInterval,
      WithTop.map_coe, toReal_zero_eq]
    cases u <;> rfl

/-- The times right of a float interval, read as reals, are those right of the interval it
denotes. -/
private theorem STLInterval.aux_toRight_toRealInterval (I : STLInterval 𝕋) : -- --- CONCL ---
    I.toRight.map STLInterval.toRealInterval = I.toRealInterval.toRight := by -- --- PROOF ---
  rcases I with _ | ⟨l, _ | u, lc, rc, _, _, _⟩
  · rfl
  · rfl
  · simp only [STLInterval.toRight, Option.map_some, STLInterval.stlInterval_toRealInterval,
      WithTop.map_top]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.getInterval_mapTime (s : TentativeKleeneSignal 𝕋)
    (I : STLInterval 𝕋) : -- --- CONCL ---
    (s.getInterval I).mapTime toReal =
      (s.mapTime toReal).getInterval I.toRealInterval := by -- --- PROOF ---
  -- making four-valued, ruling out and the constant signal, each read as reals
  have h2 : ∀ a b : PointSegmentSignal 𝕋,
      ![a.mapTime toReal, b.mapTime toReal] = (fun j => (![a, b] j).mapTime toReal) :=
    fun a b => funext fun j => match j with | 0 => rfl | 1 => rfl
  have hf : ∀ t : TentativeKleeneSignal 𝕋,
      t.toFourValued.mapTime toReal = (t.mapTime toReal).toFourValued := fun t => by
    simp only [TentativeKleeneSignal.toFourValued, TentativeKleeneSignal.mapTime, h2,
      ← PointSegmentSignal.combine_mapTime]
    rfl
  have hi : ∀ (t : TentativeKleeneSignal 𝕋) (J : STLInterval 𝕋),
      (t.setInvalid J).mapTime toReal = (t.mapTime toReal).setInvalid J.toRealInterval :=
    fun t J => by
      simp only [TentativeKleeneSignal.setInvalid, TentativeKleeneSignal.mapTime,
        PointSegmentSignal.set_mapTime]
  have hu : (FourValuedSignal.uniformSignal (𝕋 := 𝕋) .ii).mapTime toReal =
      FourValuedSignal.uniformSignal .ii := by
    rw [FourValuedSignal.uniformSignal, FourValuedSignal.indicator_mapTime]; rfl
  -- the times left and right read as reals, then the same case on both sides
  unfold TentativeKleeneSignal.getInterval
  rw [← STLInterval.aux_toLeft_toRealInterval, ← STLInterval.aux_toRight_toRealInterval]
  rcases I.toLeft with _ | left <;> rcases I.toRight with _ | right
  · exact hu
  · exact hu
  · exact hu
  · simp only [Option.map_some, hf, hi]
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

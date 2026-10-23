module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.FourValuedSignal.Operations.Combine
public import CORALean.Specification.KleeneSignal.Theorems.CombineMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalOptionMapTime

@[expose] public section

/-!
# Point-wise combination of four-valued signals at a float time type, read as reals

Over a float scalar `𝕋` the inputs are combined as Kleene signals and the inconclusive part
checked Boolean, both exactly, so the float result read as reals is the combination of the inputs
read as reals.

## Inputs
* `κ` – index type of the outputs
* `op` – pointwise operator on four-valued values
* `sig` – input signals
* `i` – output index

## Hypotheses
* none

## Conclusion
* combining commutes with reading the time points as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {ι : Type} [FinEnum ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.combine_mapTime {κ : Type} (op : (ι → FourValued) → κ → FourValued)
    (sig : ι → FourValuedSignal 𝕋) (i : κ) : -- --- CONCL ---
    (FourValuedSignal.combine op sig i).mapTime toReal =
      FourValuedSignal.combine op (fun k => (sig k).mapTime toReal) i := by -- --- PROOF ---
  -- the Kleene inputs read as reals are the float ones read as reals
  have hc : (fun j => (Sum.elim (fun k => (sig k).signal)
      (fun k => KleeneSignal.fromBoolSignal (sig k).isInconclusive) j).mapTime toReal) =
      Sum.elim (fun k => ((sig k).mapTime toReal).signal)
        (fun k => KleeneSignal.fromBoolSignal ((sig k).mapTime toReal).isInconclusive) :=
    funext fun j => by
      cases j <;> (simp [FourValuedSignal.mapTime, KleeneSignal.fromBoolSignal,
        KleeneSignal.mapTime, PointSegmentSignal.indicator_mapTime]; try rfl)
  -- the check of the inconclusive output is the float one, read as reals
  have hg : ∀ X : KleeneSignal 𝕋, (X.toBoolSignal?.getD X.signal).mapTime toReal =
      (X.mapTime toReal).toBoolSignal?.getD (X.mapTime toReal).signal := fun X => by
    rw [KleeneSignal.toBoolSignal?_mapTime]
    cases X.toBoolSignal? <;> rfl
  unfold FourValuedSignal.combine
  simp only [FourValuedSignal.mapTime, hg, KleeneSignal.combine_mapTime, hc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

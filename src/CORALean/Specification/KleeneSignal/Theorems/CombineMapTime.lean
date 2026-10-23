module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.Combine
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineMapTime

@[expose] public section

/-!
# Point-wise combination of Kleene signals at a float time type, read as reals

Over a float scalar `𝕋` both parts of the inputs are combined as Boolean signals, exactly
(`PointSegmentSignal.combine_mapTime`), so the float result read as reals is the combination of the
inputs read as reals.

## Inputs
* `κ` – index type of the outputs
* `op` – pointwise operator on Kleene values
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

theorem KleeneSignal.combine_mapTime {κ : Type} (op : (ι → Kleene) → κ → Kleene)
    (sig : ι → KleeneSignal 𝕋) (i : κ) : -- --- CONCL ---
    (KleeneSignal.combine op sig i).mapTime toReal =
      KleeneSignal.combine op (fun k => (sig k).mapTime toReal) i := by -- --- PROOF ---
  -- the parts of the inputs read as reals are the float parts read as reals
  have hc : (fun j => (Sum.elim (fun k => (sig k).signal) (fun k => (sig k).isUnknown) j).mapTime
      toReal) = Sum.elim (fun k => ((sig k).mapTime toReal).signal)
        (fun k => ((sig k).mapTime toReal).isUnknown) :=
    funext fun j => by cases j <;> rfl
  simp only [KleeneSignal.combine, KleeneSignal.mapTime, PointSegmentSignal.combine_mapTime, hc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

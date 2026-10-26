module

public import CORALean.Global.LookupMapSnd
public import CORALean.Global.MapMOptionMap
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.KleeneSignalMapTime
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.ReachSetAnalyzer.Operations.Signals

@[expose] public section

/-!
# The signals of a float analyzer, read as reals

Over a float scalar `signals` looks each proposition's builder up and builds its three-valued
signal with exact comparisons (`kleeneSignal?_mapTime`), so the float signals read as reals are the
signals of the analyzer read as reals, and both fail together.

## Inputs
* `obj` – analyzer

## Hypotheses
* none

## Conclusion
* the float signals read as reals are the real ones
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.signals_mapTime (obj : ReachSetAnalyzer 𝕋 S n) : -- --- CONCL ---
    obj.signals.map (List.map fun p => (p.1, p.2.mapTime toReal)) =
      (obj.mapTime toReal).signals := by -- --- PROOF ---
  unfold ReachSetAnalyzer.signals
  rw [mapM_option_map]
  congr 1
  funext p
  -- each proposition's builder is the float one read as reals
  have hl : (obj.mapTime toReal).sigBuilder.lookup p.1 =
      (obj.sigBuilder.lookup p.1).map (FiniteKleeneSignalBuilder.mapTime toReal) :=
    lookup_map_snd _ _ _
  rw [hl]
  cases obj.sigBuilder.lookup p.1 with
  | none => rfl
  | some b =>
    simp only [Option.map_some, Option.bind_some]
    -- and its three-valued signal the float one read as reals
    rw [← FiniteKleeneSignalBuilder.kleeneSignal?_mapTime]
    cases b.kleeneSignal? <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

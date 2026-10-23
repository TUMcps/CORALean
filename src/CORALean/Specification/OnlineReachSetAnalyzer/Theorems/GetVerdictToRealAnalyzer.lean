module

public import CORALean.Specification.FourValuedSignal.Theorems.AtMapTime
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ToRealAnalyzer

@[expose] public section

/-!
# The verdict of a float online analyzer is that of the analyzer it denotes

Over a float scalar `𝕋` the verdict is the value of the root's signal at time `0`, read exactly
(`FourValuedSignal.at_mapTime`): a float `tt` or `ff` is the verdict of the analyzer read as reals.

## Inputs
* `obj` – analyzer

## Hypotheses
* none

## Conclusion
* the verdict of the analyzer read as reals is the float verdict
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.getVerdict_toRealAnalyzer
    (obj : OnlineReachSetAnalyzer 𝕋 S d) : -- --- CONCL ---
    obj.toRealAnalyzer.getVerdict = obj.getVerdict := by -- --- PROOF ---
  -- the root's signal at `0` is read exactly
  unfold OnlineReachSetAnalyzer.getVerdict OnlineReachSetAnalyzer.toRealAnalyzer
  rcases obj.nodes with _ | ⟨n, ns⟩
  · rfl
  · simp only [List.map_cons, List.getElem?_cons_zero, Option.map_some]
    rw [← toReal_zero_eq (𝕋 := 𝕋), OnlineAnalyzerNode.toRealNode, FourValuedSignal.at_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

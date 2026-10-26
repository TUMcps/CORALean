module

public import CORALean.Global.MapMOptionMap
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.MkMapTime
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.ReachSetAnalyzer.Operations.Mk

@[expose] public section

/-!
# The constructor of a float analyzer, read as reals

Over a float scalar every proposition gets the builder of the duration, which read as reals is the
builder of the duration read as a real (`FiniteKleeneSignalBuilder.mk?_mapTime`), so the float
analyzer read as reals is the analyzer of the duration and masks read as reals, and both fail
together.

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `masks` – masks of the propositions

## Hypotheses
* none

## Conclusion
* the float analyzer read as reals is the real one
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

theorem ReachSetAnalyzer.mk?_mapTime (aps : List (String × AtomicProposition S n)) (dur : 𝕋)
    (masks : List (String × FiniteSignal 𝕋 Bool)) : -- --- CONCL ---
    (ReachSetAnalyzer.mk? aps dur masks).map (ReachSetAnalyzer.mapTime toReal) =
      ReachSetAnalyzer.mk? aps (toReal dur)
        (masks.map fun p => (p.1, p.2.mapTime toReal)) := by -- --- PROOF ---
  unfold ReachSetAnalyzer.mk?
  have h := mapM_option_map (fun p : String × AtomicProposition S n =>
    (FiniteKleeneSignalBuilder.mk? dur).map fun b => (p.1, b))
    (fun p => (p.1, p.2.mapTime toReal)) aps
  simp only [Option.map_map] at h
  -- every builder is the float builder read as reals
  have h2 : (fun a : String × AtomicProposition S n => Option.map
      ((fun p => (p.1, FiniteKleeneSignalBuilder.mapTime toReal p.2)) ∘ fun b => (a.1, b))
      (FiniteKleeneSignalBuilder.mk? dur)) =
      fun a => (FiniteKleeneSignalBuilder.mk? (toReal dur)).map fun b => (a.1, b) := by
    funext a
    rw [← FiniteKleeneSignalBuilder.mk?_mapTime, Option.map_map]
    rfl
  rw [h2] at h
  rw [← h, Option.map_map, Option.map_map]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

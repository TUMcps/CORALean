module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteSignal.Operations.Cutoff
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime

@[expose] public section

/-!
# Cutting a float signal off, read as reals

Over a float scalar `𝕋` `cutoff?` compares the duration with the cut time and counts the
breakpoints before it by exact comparisons (`TimeOrder`), so the float result read as reals is
`cutoff?` of the real signal at the real the cut time denotes, and both throw together.

## Inputs
* `V` – value type
* `s` – signal
* `dur` – cut time

## Hypotheses
* none

## Conclusion
* the float result, read as reals, is the real one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.cutoff?_mapTime {V : Type} [DecidableEq V] (s : FiniteSignal 𝕋 V)
    (dur : 𝕋) : -- --- CONCL ---
    (s.cutoff? dur).map (FiniteSignal.mapTime toReal) =
      (s.mapTime toReal).cutoff? (toReal dur) := by -- --- PROOF ---
  -- the length test and the count compare the reals the stamps denote
  have hd : (s.mapTime toReal).duration = toReal s.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq s
  have htw : ((s.mapTime toReal).time.takeWhile (· < toReal dur)).length =
      (s.time.takeWhile (· < dur)).length := by
    rw [FiniteSignal.mapTime, List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.time)
      (funext fun x => decide_eq_decide.mpr Iff.rfl))
  unfold FiniteSignal.cutoff?
  simp only [hd, htw]
  by_cases h : s.duration < dur
  · rw [if_pos h, if_pos (show toReal s.duration < toReal dur from h)]
    rfl
  · rw [if_neg h, if_neg (show ¬ toReal s.duration < toReal dur from h)]
    have := FiniteSignal.mk?_mapTime (s.time.take (s.time.takeWhile (· < dur)).length ++ [dur])
      (s.value.take ((s.time.takeWhile (· < dur)).length + 1))
    simpa [FiniteSignal.mapTime, List.map_take] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

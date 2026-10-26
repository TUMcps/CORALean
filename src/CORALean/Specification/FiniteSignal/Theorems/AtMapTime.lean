module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteSignal.Operations.At
public import CORALean.Specification.FiniteSignal.Theorems.Basic

@[expose] public section

/-!
# The value of a float signal at a time, read as reals

Over a float scalar `𝕋` `at?` compares the time with the duration and the breakpoints by exact
comparisons (`TimeOrder`), so the signal read as reals at the real the time denotes has the same
value, and both throw together.

## Inputs
* `V` – value type
* `s` – signal
* `t` – time

## Hypotheses
* none

## Conclusion
* the value on the signal and time read as reals is the float one
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

theorem FiniteSignal.at?_mapTime {V : Type} (s : FiniteSignal 𝕋 V) (t : 𝕋) : -- --- CONCL ---
    (s.mapTime toReal).at? (toReal t) = s.at? t := by -- --- PROOF ---
  -- the range test and the index count compare the reals the stamps denote
  have hd : (s.mapTime toReal).duration = toReal s.duration :=
    FiniteSignal.duration_mapTime toReal toReal_zero_eq s
  have hz : (0 ≤ toReal t) ↔ (0 ≤ t) := by
    rw [show (0 ≤ t) ↔ toReal (0 : 𝕋) ≤ toReal t from Iff.rfl, toReal_zero_eq]
  have htw : ((s.mapTime toReal).time.takeWhile (· ≤ toReal t)).length =
      (s.time.takeWhile (· ≤ t)).length := by
    rw [FiniteSignal.mapTime, List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.time)
      (funext fun x => decide_eq_decide.mpr Iff.rfl))
  unfold FiniteSignal.at?
  have hl : (s.mapTime toReal).length = s.length := by
    simp [FiniteSignal.mapTime, FiniteSignal.length]
  simp only [hd, hz, htw, hl]
  by_cases h : 0 ≤ t ∧ t ≤ s.duration
  · rw [if_pos h, if_pos (show 0 ≤ t ∧ toReal t ≤ toReal s.duration from h)]
    rfl
  · rw [if_neg h, if_neg (show ¬ (0 ≤ t ∧ toReal t ≤ toReal s.duration) from h)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

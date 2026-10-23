module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# The value at a time at a float time type, read as reals

Over a float scalar `𝕋` `at` compares the time points with the time exactly (`TimeOrder`), so the
float signal read through `toReal` has, at the real a float time denotes, the value the float signal
has at that time.

## Inputs
* `s` – signal
* `t` – time

## Hypotheses
* none

## Conclusion
* the signal read as reals has the float value at the real time
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_mapTime (s : PointSegmentSignal 𝕋) (t : 𝕋) : -- --- CONCL ---
    (s.mapTime toReal).at (toReal t) = s.at t := by -- --- PROOF ---
  -- as many points are at most the time
  have hn : ((s.timePoints.map toReal).takeWhile (· ≤ toReal t)).length =
      (s.timePoints.takeWhile (· ≤ t)).length := by
    rw [List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.timePoints)
      (funext fun x => decide_eq_decide.mpr Iff.rfl))
  -- the last of them is the time exactly when the real it denotes is
  have he : ∀ i : ℕ, (∃ b ∈ (s.timePoints.map toReal)[i]?, TimeOrder.Eqv b (toReal t)) ↔
      ∃ b ∈ s.timePoints[i]?, TimeOrder.Eqv b t := fun i => by
    rw [List.getElem?_map]
    cases s.timePoints[i]? with
    | none => simp
    | some a => simp only [Option.map_some, Option.mem_def, Option.some.injEq, exists_eq_left']; rfl
  unfold PointSegmentSignal.at
  simp only [PointSegmentSignal.mapTime, hn, he]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

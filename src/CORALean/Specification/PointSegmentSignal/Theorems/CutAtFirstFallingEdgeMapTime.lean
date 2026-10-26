module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.CutAtFirstFallingEdge

@[expose] public section

/-!
# Cutting a float signal at its first falling edge, read as reals

`cutAtFirstFallingEdge` reads only the values of a float signal and keeps a prefix of its time
points, so the cut signal read as reals is the cut of the signal read as reals.

## Inputs
* `s` – signal

## Hypotheses
* none

## Conclusion
* the cut of the signal read as reals is the float cut, read as reals
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

theorem PointSegmentSignal.cutAtFirstFallingEdge_mapTime
    (s : PointSegmentSignal 𝕋) : -- --- CONCL ---
    (s.mapTime toReal).cutAtFirstFallingEdge =
      s.cutAtFirstFallingEdge.mapTime toReal := by -- --- PROOF ---
  -- the edge is found in the values, which are the same
  unfold PointSegmentSignal.cutAtFirstFallingEdge
  have hv : (s.mapTime toReal).values = s.values := rfl
  rw [hv]
  cases (List.matlabFind id (List.zipWith (fun a b => !b && a) s.values s.values.tail)).head? with
  | none => rfl
  | some i =>
    by_cases h : i % 2 ≠ 0
    · simp [h, PointSegmentSignal.mapTime, List.map_take]
    · simp [h, PointSegmentSignal.mapTime, List.map_take]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

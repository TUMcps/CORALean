module

public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervalsBounds
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlIntervalBounds

@[expose] public section

/-!
# The intervals where a signal's values satisfy a condition, as intervals

`intervals = findIntervals(obj,cond)` of `pointSegmentSignal`: the maximal intervals of time at
which the signal has a value satisfying `cond` (by default, `true`), as the `stlInterval`s of the
bounds `findIntervalsBounds` computes.

## Inputs
* `s` – signal
* `cond` – condition on values

## Output
* the maximal intervals where the values satisfy the condition
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [Float.ExactLe 𝕋]
    [TimeOrder 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intervals = findIntervals(obj,cond)`. -/
def PointSegmentSignal.findIntervals (s : PointSegmentSignal 𝕋) (cond : Bool → Bool := id) :
    List (STLInterval 𝕋) :=
  (s.findIntervalsBounds cond).map
    (fun b => STLInterval.stlIntervalBounds b.1 b.2.1 b.2.2.1 b.2.2.2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Whether a new point is needed

`aux_isNewPointOk(obj,i,p,vals)` of `pointSegmentSignal/set.m`: whether a point at `p` with point
and interval values `vals`, replacing or inserted after the `i`-th point, is not redundant. At a
time point it must differ from the interval before it (the point `0` is always kept); inside an
interval it must differ from that interval.

## Inputs
* `T` – time type
* `s` – signal
* `i` – index of the next time point
* `p` – time of the new point
* `vals` – point and interval values of the new point

## Output
* whether a new time point is needed
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_isNewPointOk(obj,i,p,vals)`. -/
def PointSegmentSignal.isNewPointOk {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (i : ℕ) (p : T) (vals : List Bool) : Bool :=
  if s.timePoints.getD (i - 1) 0 = p then
    p = 0 ∨ vals.getD 0 false ≠ vals.getD 1 false ∨ vals.getD 0 false ≠ s.precIntervalValue i
  else vals.any (fun v => v ≠ s.succIntervalValue i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

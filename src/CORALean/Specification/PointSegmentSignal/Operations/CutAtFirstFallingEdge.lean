module

public import CORALean.Global.IsEqvTop
public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Cutting a signal where it first falls

`sig = cutAtFirstFallingEdge(obj)` of `pointSegmentSignal`: the signal up to its first falling edge,
`false` after it; the signal itself if it has no falling edge. A falling edge is a stored value
`true` followed by `false`, from a point to the interval after it, or from an interval to the next
point.

## Inputs
* `T` – time type
* `s` – signal

## Output
* the signal up to its first falling edge
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = cutAtFirstFallingEdge(obj)`. -/
def PointSegmentSignal.cutAtFirstFallingEdge {T : Type} [TimeOrder T] [Zero T]
    (s : PointSegmentSignal T) : PointSegmentSignal T :=
  -- 1. i = find(~obj.values(2:end) & obj.values(1:end-1),1,'first')
  match (List.matlabFind id (List.zipWith (fun a b => !b && a) s.values s.values.tail)).head? with
  -- 2. there is no falling edge, i.e., there is nothing to cut
  | none => s
  | some i =>
    if i % 2 ≠ 0 then
      -- falls from point to interval
      ⟨s.timePoints.take ((i + 1) / 2), s.values.take i ++ [false]⟩
    else
      -- falls from interval to point
      ⟨s.timePoints.take (i / 2 + 1), s.values.take i ++ [false, false]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import Mathlib.Order.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx

@[expose] public section

/-!
# The intervals where a signal's values satisfy a condition

`intervals = findIntervals(obj,cond)` of `pointSegmentSignal`, as the bounds `(lb,ub,lc,rc)` of the
`stlInterval(lb,ub,lc,rc)` it builds: the maximal runs of stored values satisfying `cond`, from the
rising and falling edges of `diff(take)`. `findIntervals` is the same with the intervals as
`STLInterval`s; the bounds are over any ordered time type, `ub = inf` as `⊤`.

## Inputs
* `T` – time type
* `s` – signal
* `cond` – condition on values

## Output
* the bounds of the maximal intervals where the condition holds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intervals = findIntervals(obj,cond)`, as the bounds of its intervals. -/
def PointSegmentSignal.findIntervalsBounds {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (cond : Bool → Bool := id) : List (T × WithTop T × Bool × Bool) :=
  -- 1. take = arrayfun(cond,obj.values)
  let take := s.values.map cond
  -- 2. edges = diff(take)
  let edges := List.matlabDiff take
  -- 3. falling = find(edges == -1) and rising = find(edges == 1) + 1
  let falling := List.matlabFind (· == (-1 : ℤ)) edges
  let rising := (List.matlabFind (· == (1 : ℤ)) edges).map (· + 1)
  -- 4. one interval per rising and falling edge, and one open to inf if a rising edge is left
  let later := fun (falling : List ℕ) =>
    (rising.zip falling).map (fun x =>
      ((s.precTimeAtValIdx x.1).1, (s.succTimeAtValIdx x.2).1, (s.precTimeAtValIdx x.1).2,
        (s.succTimeAtValIdx x.2).2)) ++
    (if falling.length < rising.length then
      (rising.getLast?.map (fun r => ((s.precTimeAtValIdx r).1, ⊤, (s.precTimeAtValIdx r).2,
        false))).toList else [])
  -- 5. if take(1) holds, the first interval starts at 0 and ends at the first falling edge
  if take.head? = some true then
    match falling with
    | [] => [(0, ⊤, true, false)]
    | f₁ :: falling' => (0, (s.succTimeAtValIdx f₁).1, true, (s.succTimeAtValIdx f₁).2) ::
        later falling'
  else later falling

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

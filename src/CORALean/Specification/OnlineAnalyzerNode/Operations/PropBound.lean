module

public import CORALean.Specification.STLInterval.Definitions.IsWithinTol
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# The loop of `getAllProp`

The loop of `getAllProp(obj)` of `onlineAnalyzerNode.m` over the intervals propagated to the
parents: the bound `ub` with its closedness `rc` moves to an interval's upper bound `nUb` when that
is smaller, or equal up to `withinTol` and open; an empty interval (nothing propagated to that
parent) sets `ub = 0`, open, and stops.
Real-only, a specification: it reads real time stamps exactly; its rounded refinement is the loop
of `OnlineAnalyzerNode.getAllPropFloat`.

## Inputs
* `eps` – machine epsilon

## Output
* the bound and its closedness after the intervals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop of `getAllProp`: the bound `ub` and its closedness `rc` after the intervals. -/
noncomputable def OnlineAnalyzerNode.propBound (eps : ℝ) :
    List (STLInterval ℝ) → WithTop ℝ × Bool → WithTop ℝ × Bool
  | [], st => st
  -- isemptyobject(obj.prop(i)): ub = 0; rc = false; break
  | .empty :: _, _ => (0, false)
  | .nonempty _ u _ nRc _ _ _ :: rest, (ub, rc) =>
    open Classical in
    -- if nUb < ub || withinTol(nUb,ub,eps) && ~nRc
    if STLInterval.toEReal u < STLInterval.toEReal ub ∨
        (STLInterval.IsWithinTol eps (STLInterval.toEReal u) (STLInterval.toEReal ub) ∧
          nRc = false) then
      OnlineAnalyzerNode.propBound eps rest (u, nRc)
    else OnlineAnalyzerNode.propBound eps rest (ub, rc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.STLInterval.Definitions.WithinTol

@[expose] public section

/-!
# The loop of `getAllProp`

The loop of the private `getAllProp` of `onlineAnalyzerNode.m` over the intervals propagated to
the parents: the upper bound `ub` of the smallest, and whether it is closed (`rc`). An empty entry
(nothing propagated to that parent) gives `[0,0)` and ends the loop; bounds equal within `eps`
take the open end.
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
    List STLInterval → EReal × Bool → EReal × Bool
  | [], st => st
  -- isemptyobject(obj.prop(i)): ub = 0; rc = false; break
  | .empty :: _, _ => (0, false)
  | .nonempty _ u _ nRc _ _ _ :: rest, (ub, rc) =>
    open Classical in
    -- if nUb < ub || withinTol(nUb,ub,eps) && ~nRc
    if u < ub ∨ (STLInterval.withinTol eps u ub ∧ nRc = false) then
      OnlineAnalyzerNode.propBound eps rest (u, nRc)
    else OnlineAnalyzerNode.propBound eps rest (ub, rc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

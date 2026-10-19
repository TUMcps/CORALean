module

public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.STLInterval.Definitions.WithinTol
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# The time up to which everything is propagated

`allProp = getAllProp(obj)` of `onlineAnalyzerNode.m` (a private method): the interval from `0` to
the smallest upper bound of the intervals propagated to the parents, closed at its end if that
bound's interval is; an empty entry (nothing propagated to that parent) gives `[0,0)`, and no
parent at all `[0,∞)`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
intervals over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop of `getAllProp`: the bound `ub` and its closedness `rc` after the intervals. -/
noncomputable def OnlineAnalyzerNode.aux_propBound (eps : ℝ) :
    List STLInterval → EReal × Bool → EReal × Bool
  | [], st => st
  -- isemptyobject(obj.prop(i)): ub = 0; rc = false; break
  | .empty :: _, _ => (0, false)
  | .nonempty _ u _ nRc _ _ _ _ :: rest, (ub, rc) =>
    open Classical in
    -- if nUb < ub || withinTol(nUb,ub,eps) && ~nRc
    if u < ub ∨ (STLInterval.withinTol eps u ub ∧ nRc = false) then
      OnlineAnalyzerNode.aux_propBound eps rest (u, nRc)
    else OnlineAnalyzerNode.aux_propBound eps rest (ub, rc)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `allProp = getAllProp(obj)`. -/
noncomputable def OnlineAnalyzerNode.getAllProp (eps : ℝ) (n : OnlineAnalyzerNode A) :
    STLInterval :=
  -- ub = inf; rc = true; the loop; allProp = stlInterval(0,ub,true,rc)
  let b := OnlineAnalyzerNode.aux_propBound eps n.prop (⊤, true)
  STLInterval.stlInterval 0 b.1 true b.2 le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

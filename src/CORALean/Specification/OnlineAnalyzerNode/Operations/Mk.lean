module

public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# The node constructor

`obj = onlineAnalyzerNode(type,idx,parents,dropPropagated,varargin)`: a node with the signal its
type starts with, nothing propagated to any parent yet (`prop` is one empty interval per parent)
and no children. An `until` node takes its interval as the extra argument, the other types none
(`narginchk`), and an `AP` node takes its atomic proposition, which is not stored here; CORA
throws otherwise, here `none`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj = onlineAnalyzerNode(type,idx,parents,dropPropagated,varargin)`. -/
noncomputable def OnlineAnalyzerNode.mk? (kind : OnlineAnalyzerNode.Kind) (idx : ℕ)
    (parents : List ℕ) (dropPropagated : Bool) (interval : Option STLInterval) :
    Option OnlineAnalyzerNode :=
  -- narginchk: an `until` node gets its interval, no other node does
  if decide (kind = .until) = interval.isSome then
    some { kind := kind, signal := OnlineAnalyzerNode.initSignal kind,
           prop := parents.map (fun _ => STLInterval.empty), dropPropagated := dropPropagated,
           idx := idx, parents := parents, children := [], interval := interval,
           tentative := if kind = .ap then some TentativeKleeneSignal.emptySignal else none }
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

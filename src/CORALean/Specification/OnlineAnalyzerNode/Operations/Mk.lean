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

## Inputs
* `kind` – node kind
* `idx` – node index
* `parents` – parent indices
* `dropPropagated` – drop propagated times from the signal
* `interval` – interval of an until node
* `ap` – proposition of an atomic node

## Output
* the new node, or none if the arguments do not fit its kind
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj = onlineAnalyzerNode(type,idx,parents,dropPropagated,varargin)`. -/
def OnlineAnalyzerNode.mk? [Float.ExactLe 𝕋] [TimeOrder 𝕋] (kind : OnlineAnalyzerNode.Kind)
    (idx : ℕ) (parents : List ℕ) (dropPropagated : Bool) (interval : Option (STLInterval 𝕋))
    (ap : Option A) : Option (OnlineAnalyzerNode 𝕋 A) :=
  -- narginchk: an `until` node gets its interval, an `AP` node its proposition, no other one
  if decide (kind = .until) = interval.isSome ∧ decide (kind = .ap) = ap.isSome then
    some { kind := kind, signal := OnlineAnalyzerNode.initSignal kind,
           prop := parents.map (fun _ => STLInterval.empty), dropPropagated := dropPropagated,
           idx := idx, parents := parents, children := [], interval := interval, ap := ap,
           tentative := if kind = .ap then some TentativeKleeneSignal.emptySignal else none }
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

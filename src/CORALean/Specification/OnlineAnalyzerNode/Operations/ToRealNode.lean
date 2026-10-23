module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.STLInterval.Operations.ToRealInterval
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# A node at a float time type, read as reals

The node whose signals have the reals the float time points denote and whose intervals are
those the float ones denote (`toRealInterval`): what a float node means. The soundness of the
float online analysis is stated through it.

## Inputs
* `n` – node

## Output
* the node over `ℝ` with the denoted time points and intervals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The node read as reals: every time point and interval mapped, the rest kept. -/
def OnlineAnalyzerNode.toRealNode (n : OnlineAnalyzerNode 𝕋 A) : OnlineAnalyzerNode ℝ A :=
  { kind := n.kind, signal := n.signal.mapTime toReal, prop := n.prop.map (·.toRealInterval),
    dropPropagated := n.dropPropagated, idx := n.idx, parents := n.parents,
    children := n.children, interval := n.interval.map (·.toRealInterval), ap := n.ap,
    tentative := n.tentative.map (·.mapTime toReal) }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

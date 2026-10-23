module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ToRealNode
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# An online analyzer at a float time type, read as reals

The analyzer whose nodes are read as reals (`toRealNode`), the rest kept: what a float analyzer
means. The soundness of its verdict is stated through it.

## Inputs
* `obj` – analyzer

## Output
* the analyzer over `ℝ` with the nodes read as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The analyzer read as reals: every node read as reals, the rest kept. -/
def OnlineReachSetAnalyzer.toRealAnalyzer (obj : OnlineReachSetAnalyzer 𝕋 S d) :
    OnlineReachSetAnalyzer ℝ S d :=
  { propagationFrequency := obj.propagationFrequency, nodes := obj.nodes.map (·.toRealNode),
    leaves := obj.leaves, numObservations := obj.numObservations, propagated := obj.propagated }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

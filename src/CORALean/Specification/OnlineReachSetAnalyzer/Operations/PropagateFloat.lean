module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateRecFloat

@[expose] public section

/-!
# Propagating the observations, over a float scalar

`propagate(obj,makeValid)` with time stamps in `𝕋`: reset `obj.propagated` and propagate from the
root, node `1`, by the recursion of `propagateRec` with each node propagated by
`OnlineAnalyzerNode.propagateFloat` (`propagateFloat_toRealNode` says what a step does). `fuel`
bounds the recursion; running out of it is `none`, as is every throw.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer
* `makeValid` – interval to make final

## Output
* the analyzer after propagating from the root, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `propagate(obj,makeValid)`. -/
def OnlineReachSetAnalyzer.propagateFloat (eps : 𝕋) (obj : OnlineReachSetAnalyzer 𝕋 S d)
    (makeValid : STLInterval 𝕋) : Option (OnlineReachSetAnalyzer 𝕋 S d) :=
  -- obj.propagated = false(1,length(obj.nodes)); obj.propagateRec(makeValid,1)
  (OnlineReachSetAnalyzer.propagateRecFloat eps makeValid (obj.nodes.length + 1) 1
    (obj.nodes, List.replicate obj.nodes.length false)).map fun st =>
      { obj with nodes := st.1, propagated := st.2 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

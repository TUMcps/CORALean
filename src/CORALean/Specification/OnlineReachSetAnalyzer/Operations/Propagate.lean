module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateRec

@[expose] public section

/-!
# Propagating the observations

`propagate(obj,makeValid)` (a private method): reset `obj.propagated` and propagate from the root,
node `1`, with the interval `makeValid` for which observations are final. `eps` is MATLAB's
`eps`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
intervals over `𝕋`, rounded outward) is not yet written.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer
* `makeValid` – interval to make final

## Output
* the analyzer after propagating from the root, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `propagate(obj,makeValid)`. -/
noncomputable def OnlineReachSetAnalyzer.propagate (eps : ℝ) (obj : OnlineReachSetAnalyzer S d)
    (makeValid : STLInterval) : Option (OnlineReachSetAnalyzer S d) :=
  -- obj.propagated = false(1,length(obj.nodes)); obj.propagateRec(makeValid,1)
  (OnlineReachSetAnalyzer.propagateRec eps makeValid (obj.nodes.length + 1) 1
    (obj.nodes, List.replicate obj.nodes.length false)).map fun st =>
      { obj with nodes := st.1, propagated := st.2 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

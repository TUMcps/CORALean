module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateRec

@[expose] public section

/-!
# Propagating the observations

`propagate(obj,makeValid)` (a private method): reset `obj.propagated` and propagate from the root,
node `1`, with the interval `makeValid` for which observations are final. `eps` is MATLAB's
`eps`.

Real-only, a specification: it reads real time stamps exactly; its rounded refinement is
`OnlineReachSetAnalyzer.propagateFloat`.

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
noncomputable def OnlineReachSetAnalyzer.propagate (eps : ℝ) (obj : OnlineReachSetAnalyzer ℝ S d)
    (makeValid : STLInterval ℝ) : Option (OnlineReachSetAnalyzer ℝ S d) :=
  -- obj.propagated = false(1,length(obj.nodes)); obj.propagateRec(makeValid,1)
  (OnlineReachSetAnalyzer.propagateRec eps makeValid (obj.nodes.length + 1) 1
    (obj.nodes, List.replicate obj.nodes.length false)).map fun st =>
      { obj with nodes := st.1, propagated := st.2 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer

@[expose] public section

/-!
# The verdict so far

`verdict = getVerdict(obj)`: the satisfaction signal of the root node at time `0`. CORA fails for
an analyzer without nodes; here `none`.

## Inputs
* `obj` – analyzer

## Output
* the root's verdict at time zero, or none without nodes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `verdict = getVerdict(obj)`. -/
noncomputable def OnlineReachSetAnalyzer.getVerdict (obj : OnlineReachSetAnalyzer S d) :
    Option FourValued :=
  obj.nodes[0]?.map fun n => n.signal.at 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

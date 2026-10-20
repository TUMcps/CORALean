module

public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula

@[expose] public section

/-!
# The node type of a subformula

`phi.type` of `parse`, as the type of node made for it: `true`, `false`, `AP`, `~`, `&`, `|`,
`until`.

## Inputs
* none

## Output
* the node type made for the subformula
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `phi.type`. -/
def OnlineReachSetAnalyzer.Formula.kind : OnlineReachSetAnalyzer.Formula A →
    OnlineAnalyzerNode.Kind
  | .tt => .true
  | .ff => .false
  | .ap _ _ => .ap
  | .not _ => .not
  | .and _ _ => .and
  | .or _ _ => .or
  | .until _ _ _ => .until

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

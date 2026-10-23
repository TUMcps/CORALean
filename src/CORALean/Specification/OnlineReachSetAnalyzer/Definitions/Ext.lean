module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Same

@[expose] public section

/-!
# A list of nodes that grew

`nodes'` extends `nodes`: it is at least as long, and each node of `nodes` is in `nodes'` at the
same position up to its graph edges (`Same`).

## Inputs
* `nodes` – list of nodes
* `nodes'` – extended list

## Output
* the second list is at least as long and keeps each node's fixed fields
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nodes'` is `nodes` with edges added and nodes appended. -/
def OnlineReachSetAnalyzer.Ext (nodes nodes' : List (OnlineAnalyzerNode ℝ A)) : Prop :=
  nodes.length ≤ nodes'.length ∧ ∀ (j : ℕ) (h : j < nodes.length) (h' : j < nodes'.length),
    OnlineReachSetAnalyzer.Same nodes[j] nodes'[j]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

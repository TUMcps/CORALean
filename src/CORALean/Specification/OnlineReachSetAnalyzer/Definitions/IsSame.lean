module

public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# Nodes that differ only by their graph edges

The fields of a node that parsing never changes once the node exists: its `idx`, `kind`,
`dropPropagated` and the first of its `parents` (a parent is only added at the end of the list).

## Inputs
* `n` – first node
* `n'` – second node

## Output
* the nodes agree in index, kind, flag and first parent
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two nodes agree in `idx`, `kind`, `dropPropagated` and the first parent. -/
def OnlineReachSetAnalyzer.IsSame (n n' : OnlineAnalyzerNode ℝ A) : Prop :=
  n.idx = n'.idx ∧ n.kind = n'.kind ∧ n.parents.head? = n'.parents.head? ∧
    n.dropPropagated = n'.dropPropagated

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

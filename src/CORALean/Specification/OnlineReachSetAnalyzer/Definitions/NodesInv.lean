module

public import CORALean.Specification.OnlineAnalyzerNode.OnlineAnalyzerNode

@[expose] public section

/-!
# What parsing keeps true of the nodes

Node `j` (from `0`) has index `j + 1`, and every node has the `dropPropagated` of the
constructor and a first parent.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The invariant of the nodes made by `parse`. -/
def OnlineReachSetAnalyzer.NodesInv (dropPropagated : Bool)
    (nodes : List (OnlineAnalyzerNode A)) : Prop :=
  (∀ (j : ℕ) (h : j < nodes.length), nodes[j].idx = j + 1) ∧
    ∀ n ∈ nodes, n.dropPropagated = dropPropagated ∧ n.parents.head?.isSome = true

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

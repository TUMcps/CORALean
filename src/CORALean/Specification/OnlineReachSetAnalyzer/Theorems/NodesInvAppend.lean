module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.NodesInv

@[expose] public section

/-!
# The invariant survives a new node

A node with the next index, the right `dropPropagated` and a parent, appended to a list with the
invariant, keeps it.

## Inputs
* `dp` – drop propagated times flag
* `nodes` – list of nodes
* `node` – node to append

## Hypotheses
* `h` – the list satisfies the invariant
* `hidx` – the node has the next index
* `hd` – the node has the same flag
* `hp` – the node has a parent

## Conclusion
* the extended list satisfies the invariant
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.nodesInv_append (dp : Bool) (nodes : List (OnlineAnalyzerNode A))
    (node : OnlineAnalyzerNode A) (h : OnlineReachSetAnalyzer.NodesInv dp nodes)
    (hidx : node.idx = nodes.length + 1) (hd : node.dropPropagated = dp)
    (hp : node.parents.head?.isSome = true) : -- --- CONCL ---
    OnlineReachSetAnalyzer.NodesInv dp (nodes ++ [node]) := by -- --- PROOF ---
  refine ⟨fun j hj => ?_, fun n hn => ?_⟩
  -- the positions of the old nodes and of the new one
  · by_cases hjl : j < nodes.length
    · rw [List.getElem_append_left hjl]
      exact h.1 j hjl
    · have : j = nodes.length := by simp at hj; omega
      subst this
      simpa [List.getElem_append_right] using hidx
  -- every node, old or new
  · rcases List.mem_append.mp hn with hn | hn
    · exact h.2 n hn
    · obtain rfl : n = node := by simpa using hn
      exact ⟨hd, hp⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

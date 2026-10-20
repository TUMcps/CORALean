module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Ext
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.NodesInv

@[expose] public section

/-!
# The invariant survives a change of edges

If `nodes'` is `nodes` with edges added (an extension of the same length), it keeps the invariant
of `nodes`.

## Inputs
* `dp` – drop propagated times flag
* `nodes` – list of nodes
* `nodes'` – extended list

## Hypotheses
* `hl` – both lists have equal length
* `he` – the second list extends the first
* `h` – the first list satisfies the invariant

## Conclusion
* the second list satisfies the invariant
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.nodesInv_of_ext (dp : Bool)
    (nodes nodes' : List (OnlineAnalyzerNode A)) (hl : nodes'.length = nodes.length)
    (he : OnlineReachSetAnalyzer.Ext nodes nodes')
    (h : OnlineReachSetAnalyzer.NodesInv dp nodes) : -- --- CONCL ---
    OnlineReachSetAnalyzer.NodesInv dp nodes' := by -- --- PROOF ---
  refine ⟨fun j hj => ?_, fun n hn => ?_⟩
  -- the index of a node is unchanged
  · rw [← (he.2 j (by omega) hj).1]
    exact h.1 j (by omega)
  -- and so is the rest
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hn
    have hs := he.2 j (by omega) hj
    obtain ⟨hd, hp⟩ := h.2 nodes[j] (List.getElem_mem _)
    refine ⟨hs.2.2.2.symm.trans hd, ?_⟩
    rw [← hs.2.2.1]
    exact hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

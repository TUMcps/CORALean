module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Ext
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec

@[expose] public section

/-!
# Updating a node keeps the list

If `f` keeps every node of the list it is applied to up to `Same`, updating one node gives a list of
the same length that extends the old one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.ext_updateNode (nodes nodes' : List (OnlineAnalyzerNode A)) (i : ℕ)
    (f : OnlineAnalyzerNode A → Option (OnlineAnalyzerNode A))
    (h : OnlineReachSetAnalyzer.updateNode nodes i f = some nodes')
    (hf : ∀ n ∈ nodes, ∀ n', f n = some n' → OnlineReachSetAnalyzer.Same n n') : -- --- STMT ---
    OnlineReachSetAnalyzer.Ext nodes nodes' ∧ nodes'.length = nodes.length := by -- --- PROOF ---
  obtain ⟨-, n, n', hn, hfn, rfl⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).mp h
  refine ⟨⟨by simp, fun j hj hj' => ?_⟩, by simp⟩
  -- the updated position is `Same`, every other one is equal
  rw [List.getElem_set]
  by_cases hji : i - 1 = j
  · rw [if_pos hji]
    have : nodes[j] = n := by subst hji; exact (List.getElem?_eq_some_iff.mp hn).2
    rw [this]
    exact hf n (List.mem_of_getElem? hn) n' hfn
  · rw [if_neg hji]
    exact OnlineReachSetAnalyzer.same_refl _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

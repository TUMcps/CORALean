module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Basic

@[expose] public section

/-!
# What `updateNode` does

Updating the node with index `i` succeeds exactly for `i ≠ 0`, an existing node and a succeeding
`f`, and replaces that node by `f` of it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.updateNode_eq_some_iff {B : Type} (nodes : List B) (i : ℕ)
    (f : B → Option B) (nodes' : List B) : -- --- CONCL ---
    OnlineReachSetAnalyzer.updateNode nodes i f = some nodes' ↔
      i ≠ 0 ∧ ∃ n n', nodes[i - 1]? = some n ∧ f n = some n' ∧
        nodes' = nodes.set (i - 1) n' := by -- --- PROOF ---
  unfold OnlineReachSetAnalyzer.updateNode
  by_cases hi : i = 0
  · simp [hi]
  · simp only [ne_eq, hi, not_false_eq_true, true_and]
    constructor
    · intro h
      obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨n', hn', h⟩ := Option.map_eq_some_iff.mp h
      exact ⟨n, n', hn, hn', h.symm⟩
    · rintro ⟨n, n', hn, hn', rfl⟩
      simp [hn, hn']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

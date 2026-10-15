module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate

@[expose] public section

/-!
# Propagating at a constant

A `true` or `false` node propagates nothing: the node and its children stay as they are.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `true` or `false` node propagates nothing. -/
theorem OnlineAnalyzerNode.propagate_leaf (eps : ℝ) (n : OnlineAnalyzerNode A)
    (ch : List (OnlineAnalyzerNode A)) (I : STLInterval) (h : n.kind = .true ∨ n.kind = .false) :
    n.propagate eps ch I = some (n, ch) := by
  unfold OnlineAnalyzerNode.propagate
  rcases h with h | h <;> rw [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

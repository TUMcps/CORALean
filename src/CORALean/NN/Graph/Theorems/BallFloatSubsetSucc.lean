module

public import CORALean.NN.Graph.Operations.BallFloat

@[expose] public section

/-!
# The float ball grows with the radius
`GNN.ballFloat E v r ⊆ GNN.ballFloat E v (r + 1)`: staying put is one of the hops [1, §4.3].

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.ballFloat_subset_succ (E : Fin N → Fin N → Bool) (v : Fin N) (r : ℕ) :
    GNN.ballFloat E v r ⊆ GNN.ballFloat E v (r + 1) := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, j, hj, Or.inl rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

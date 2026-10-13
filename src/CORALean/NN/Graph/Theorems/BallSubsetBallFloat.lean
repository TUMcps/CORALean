import CORALean.NN.Graph.Operations.Ball
import CORALean.NN.Graph.Operations.BallFloat

/-!
# The real ball lies in the ball on an edge test that covers the support
If `E` is `true` wherever `A` is nonzero, `GNN.ballFloat E v r` contains `GNN.ball A v r` at
every radius [1, §4.3].

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

theorem GNN.ball_subset_ballFloat (A : Mat ℝ N N) (E : Fin N → Fin N → Bool)
    (hE : ∀ i j, A i j ≠ 0 → E i j = true) (v : Fin N) (r : ℕ) :
    Real.GNN.ball A v r ⊆ GNN.ballFloat E v r := by -- --- PROOF ---
  induction r with
  | zero => exact subset_refl _
  | succ r ih =>
      intro j hj
      obtain ⟨_, i, hi, hij⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, ih hi, hij.imp id (hE i j)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Graph.Operations.Bfs
public import CORALean.NN.Graph.Theorems.BallMono
public import CORALean.NN.Graph.Theorems.MemBallSelf

@[expose] public section

/-!
# The breadth-first search finds the ball

`[1, Sec. 4.3]`: the nodes `bfs` has visited after `r` hops are exactly `ball A v r`. Expanding the
frontier alone loses nothing: an edge out of a node reached at an earlier hop leads into the ball
already, so a node outside the ball is reached only from the frontier. The invariant carries that
with the frontier lying in the ball: every node of the ball is on the frontier or in a smaller ball.

## Inputs
* `A` – adjacency matrix
* `v` – start node
* `r` – number of hops

## Hypotheses
* none

## Conclusion
* the visited nodes of the search are the ball

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The invariant of the search at hop `r`. -/
theorem aux_bfs_inv (A : Mat ℝ N N) (v : Fin N) (r : ℕ) :
    (GNN.bfs A v r).1 = GNN.ball A v r ∧ (GNN.bfs A v r).2 ⊆ GNN.ball A v r ∧
      ∀ i ∈ GNN.ball A v r, i ∈ (GNN.bfs A v r).2 ∨
        ∃ r' < r, i ∈ GNN.ball A v r' := by -- --- PROOF ---
  induction r with
  | zero =>
    refine ⟨rfl, by simp [GNN.bfs, GNN.ball], fun i hi => Or.inl ?_⟩
    simpa [GNN.bfs, GNN.ball] using hi
  | succ r ih =>
    obtain ⟨hvis, hfr, hcov⟩ := ih
    -- a node outside the ball with a neighbour in it has that neighbour on the frontier
    have hkey : ∀ i j, i ∈ GNN.ball A v r → A i j ≠ 0 → j ∉ GNN.ball A v r →
        i ∈ (GNN.bfs A v r).2 := by
      intro i j hi hij hj
      rcases hcov i hi with h | ⟨r', hr', hi'⟩
      · exact h
      · exact absurd (GNN.ball_mono A v (Nat.succ_le_of_lt hr')
          (by simp only [GNN.ball, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hi', Or.inr hij⟩)) hj
    have hnext : ∀ j, j ∈ (GNN.bfs A v (r + 1)).2 ↔
        j ∉ GNN.ball A v r ∧ ∃ i ∈ (GNN.bfs A v r).2, A i j ≠ 0 := by
      intro j
      simp [GNN.bfs, hvis]
    -- the visited set after the hop is the ball
    have hvis' : (GNN.bfs A v (r + 1)).1 = GNN.ball A v (r + 1) := by
      ext j
      simp only [GNN.bfs, hvis, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        GNN.ball]
      constructor
      · rintro (h | ⟨-, i, hi, hij⟩)
        · exact ⟨j, h, Or.inl rfl⟩
        · exact ⟨i, hfr hi, Or.inr hij⟩
      · rintro ⟨i, hi, hij | hij⟩
        · exact Or.inl (hij ▸ hi)
        · by_cases hj : j ∈ GNN.ball A v r
          · exact Or.inl hj
          · exact Or.inr ⟨hj, i, hkey i j hi hij hj, hij⟩
    -- the frontier lies in the ball, and every node of the new ball is on it or in the old one
    refine ⟨hvis', ?_, fun j hj => ?_⟩
    · intro j hj
      have := (hnext j).mp hj
      obtain ⟨-, i, hi, hij⟩ := this
      simp only [GNN.ball, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hfr hi, Or.inr hij⟩
    · by_cases hjr : j ∈ GNN.ball A v r
      · exact Or.inr ⟨r, Nat.lt_succ_self r, hjr⟩
      · left
        simp only [GNN.ball, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨i, hi, hij | hij⟩ := hj
        · exact absurd (hij ▸ hi) hjr
        · exact (hnext j).mpr ⟨hjr, i, hkey i j hi hij hjr, hij⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3]: the nodes the breadth-first search has visited within `r` hops are the ball. -/
theorem GNN.bfs_visited (A : Mat ℝ N N) (v : Fin N) (r : ℕ) :
    (GNN.bfs A v r).1 = GNN.ball A v r := (aux_bfs_inv A v r).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The breadth-first search for a node's neighbourhood

`[1, Sec. 4.3]`: the `(κ' + 1)`-hop neighbourhood "can easily be found using a breadth-first
search on the given graph with the considered node as the root node". `bfs A v r` is the pair of
the nodes reached within `r` hops and the frontier, those first reached at hop `r`: a hop expands
the frontier alone, along the edges `A i j ≠ 0`, and keeps what has not been reached before.
`GNN.ball` filters every node at every radius instead; `bfs_visited` says the two are one set.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(visited, frontier)` after `r` hops from `v`: the frontier's unvisited neighbours join. -/
noncomputable def GNN.bfs (A : Mat ℝ N N) (v : Fin N) : ℕ → Finset (Fin N) × Finset (Fin N)
  | 0 => ({v}, {v})
  | r + 1 =>
    let reached := GNN.bfs A v r                                        -- (visited, frontier)
    let next := Finset.univ.filter fun j => j ∉ reached.1 ∧ ∃ i ∈ reached.2, A i j ≠ 0
    (reached.1 ∪ next, next)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

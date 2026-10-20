module

public import CORALean.NN.Graph.Operations.Ball

@[expose] public section

/-!
# The ball depends on the matrix only through its support

If `A'` is nonzero wherever `A` is, `A'`'s ball only ever grows over `A`'s: the
filter `ball`'s recursion runs, `i = j ∨ A i j ≠ 0`, reads `A` through the same
disjunct, so a larger support can only add more `j` at each successor radius.

This is what makes a single subgraph usable across every graph in a family that
shares a support bound — `A` need not be fixed, only its zero pattern.

## Inputs
* `A` – adjacency matrix
* `A'` – adjacency matrix with the larger support
* `v` – center node
* `r` – radius in hops

## Hypotheses
* `h` – support of A is contained in that of A'

## Conclusion
* the ball of A is contained in the ball of A'
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A matrix whose support contains another's has an only-larger ball, at every
radius. -/
theorem GNN.ball_mono_of_support {A A' : Mat ℝ N N} (h : ∀ i j, A i j ≠ 0 → A' i j ≠ 0)
    (v : Fin N) (r : ℕ) : -- --- CONCL ---
    GNN.ball A v r ⊆ GNN.ball A' v r := by -- --- PROOF ---
  induction r with
  | zero => exact subset_refl _
  | succ r ih =>
      intro j hj
      obtain ⟨_, i, hi, hij⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, ih hi, hij.imp id (h i j)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

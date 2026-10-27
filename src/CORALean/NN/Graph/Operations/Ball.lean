module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The `r`-hop ball around a node, `[1, §4.3]`'s locality neighbourhood

`ball A v r` grows outward one message-passing hop at a time: a node joins at radius `r + 1` exactly
when some node already at radius `r` reaches it, by being it (`i = j`) or by an edge (`A i j ≠ 0`).
The `i = j` disjunct is not padding: message passing runs on `Ã = A + I`, and it makes `ball`
monotone in `r` for free.

Radius `L`, not `L + 1`: an `L`-step chain's row `v` depends only on `ball A v L`
(`EvalStepsRowMask`). The extra hop `[1, §4.3]` needs is for *computing* `P = D̃^(-1/2) Ã
D̃^(-1/2)`.

## Inputs
* `A` – adjacency matrix
* `v` – center node

## Output
* nodes within r hops of the center, for each radius r

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `r`-hop neighbourhood of `v` on `Ã = A + I`: `v` itself at radius `0`, and
one more hop of `A`'s edges (or staying put) at each successor radius. -/
noncomputable def GNN.ball (A : Mat ℝ N N) (v : Fin N) : ℕ → Finset (Fin N)
  | 0 => {v}
  | r + 1 => Finset.univ.filter fun j => ∃ i ∈ GNN.ball A v r, i = j ∨ A i j ≠ 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

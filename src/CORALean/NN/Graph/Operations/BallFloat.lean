module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# The `r`-hop neighbourhood on an edge test
`GNN.ballFloat E v r` is `GNN.ball` with the test `A i j ≠ 0` replaced by a Boolean `E i j`, so it
runs: `v` itself at radius `0`, and one more hop of `E`'s edges (or staying put) at each successor
radius [1, §4.3]. With `E = GNN.support A` it is the neighbourhood of a float adjacency matrix;
with any larger `E`, a larger one.

## Inputs
* `E` – Boolean edge test
* `v` – center node

## Output
* nodes within r hops of the center, for each radius r

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


-- =====================================  MAIN DEFINITION  ====================================== --

def GNN.ballFloat (E : Fin N → Fin N → Bool) (v : Fin N) : ℕ → Finset (Fin N)
  | 0 => {v}
  | r + 1 => Finset.univ.filter fun j => ∃ i ∈ GNN.ballFloat E v r, i = j ∨ E i j = true

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

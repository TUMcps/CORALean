import CORALean.NN.Graph.Conv

/-!
# The `r`-hop ball around a node, `[1, §4.3]`'s locality neighbourhood

`ball A v r` grows outward one message-passing hop at a time: a node joins at
radius `r + 1` exactly when some node already at radius `r` reaches it, either
by being it (`i = j`) or by an edge (`A i j ≠ 0`). The `i = j` disjunct is not
padding — message passing runs on `Ã = A + I`, so every node is its own
neighbour, and it is what makes `ball` monotone in `r` for free, with no
separate union needed.

Radius `L`, not `L + 1`: `evalSteps` is stated at an arbitrary `Pm`, so an
`L`-step chain's row `v` depends only on `ball A v L` (`EvalStepsRowMask`). The
extra hop `[1, §4.3]` needs is for *computing* `P = D̃^(-1/2) Ã D̃^(-1/2)` from
`A`, whose entries read the degrees of both endpoints — a fact about
`messagePassing` itself, stated at `[1, §4.3]`'s caller, not here.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


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

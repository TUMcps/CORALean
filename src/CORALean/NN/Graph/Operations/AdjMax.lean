import CORALean.NN.Graph.Operations.AdjAt

/-!
# The adjacency with every uncertain edge present

`adjAt A U lam` at `lam := fun _ => 1`: every uncertain edge weighted as heavily
as an admissible `lam` ever allows. `Theorems/AdjAtSupportSubset.lean` is why
this is worth naming — its ball dominates the ball of every admissible `adjAt`,
so `adjMax` is the one graph `[1, §4.3]`'s subgraph reduction needs to be sized
against, uniformly in `lam`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The adjacency at every uncertain edge weighted `1`, the heaviest an
admissible `lam` ever assigns. -/
def GNN.adjMax (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) : Mat ℝ N N :=
  GNN.adjAt A U (fun _ => 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.NN.Graph.Operations.AdjAt
public import CORALean.NN.Graph.Operations.Degree

@[expose] public section

/-!
# The degree of a graph whose edges are uncertain, at one choice of weights

[1]'s degree matrix `D̃ = diag(1 Ã)`, read at `Ã = A(λ) + I` and one node at a
time. `degree` and `degreeSup` are the two ends of the range `degreeAt` can
take, at all weights `0` and at all weights `1`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Node `j`'s degree at one choice of edge weights. -/
def GNN.degreeAt (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ)
    (j : Fin N) : ℝ :=
  GNN.degree (GNN.adjAt A U lam) j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

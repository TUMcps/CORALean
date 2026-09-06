import CORALean.NN.Graph.Conv
import CORALean.NN.Graph.Uncertain

/-!
# The degree of a graph whose edges are uncertain

[1]'s degree matrix `D̃ = diag(1 Ã)`, read at `Ã = A(λ) + I` and one node at a
time. It is affine in the edge weights: each uncertain edge contributes its own
weight times that edge's column sum at `j`, and nothing else moves. `degreeInf`
and `degreeSup` are the two ends of that range, at all weights `0` and at all
weights `1`; `Theorems/UncertainDegreeBounds.lean` brackets `degreeAt` by them.

The bounds are plain reals rather than a polynomial zonotope of degrees: what
reads them is an enclosure of `x ↦ x^(-1/2)` over an interval, which needs the
two ends and not the dependence on the individual edges.

`degreeInf` takes the uncertain edges and does not read them, which is what the
`_U` says. The two bounds are read as a pair, and one of them silently taking
fewer arguments than the other is a seam a caller would have to remember.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}

/-- Node `j`'s degree at one choice of edge weights. -/
def GNN.degreeAt (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ)
    (j : Fin N) : ℝ :=
  GNN.degree (GNN.adjAt A U lam) j

/-- What the uncertain edges at `j` can add: `edgeMat`'s column sum. -/
def GNN.edgeDegree (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  ∑ e, ∑ i, GNN.edgeMat (U e) i j


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The degree at `j` with every uncertain edge switched off. -/
def GNN.degreeInf (A : Mat ℝ N N) (_U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  GNN.degree A j

/-- The degree at `j` with every uncertain edge switched on. -/
def GNN.degreeSup (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  GNN.degree A j + GNN.edgeDegree U j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

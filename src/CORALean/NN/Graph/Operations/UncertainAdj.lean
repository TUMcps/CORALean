import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.NN.Graph.Operations.EdgeMat

/-!
# The adjacency of a graph whose edges are uncertain

[1]'s uncertain graph structure, as one matrix polynomial zonotope: one
dependent factor and one dependent generator per uncertain edge, and no
independent block — a factor `α` in the unit interval around zero *is* the
weight `λ = (1 + α)/2` (`smul_edge_half`), which is the whole construction.
Keeping the factor dependent stops one edge counting as fresh uncertainty at
each step of a chain.

Real only: `Float.PolyZonotope` is indexed by ℕ over `Vec`, so a float matrix
polynomial zonotope is a representation to build before this gets a float half.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s uncertain adjacency: one dependent factor and one dependent generator
per uncertain edge, and no independent block at all. -/
noncomputable def GNN.uncertainAdj (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) :
    PolyZonotope (Mat ℝ N N) where
  p := m
  h := m
  q := 0
  c := A + ∑ e, (1/2 : ℝ) • GNN.edgeMat (U e)
  G := fun e => (1/2 : ℝ) • GNN.edgeMat (U e)
  E := PolyZonotope.identE m
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# The adjacency of a graph whose edges are uncertain

[1]'s uncertain graph structure. The fixed edges are already in `A`; each
uncertain edge is given by its endpoints and carries a weight anywhere in the
interval from `0` to `1`. `adjAt` is the adjacency at one choice of those
weights, `uncertainAdj` the matrix polynomial zonotope of all of them at once.

One dependent factor and one dependent generator per uncertain edge, and no
independent block: a factor `α` in the unit interval around zero *is* the weight
`λ = (1 + α)/2`, and that change of variable — `smul_edge_half`, read by every
set built over these factors — is the whole construction. Keeping the factor
dependent stops one edge counting as fresh uncertainty at each step of a chain.

`edgeMat` writes both orientations at once, so an edge costs one factor and not
two — the adjacency a convolution reads is symmetric.

Real only: `Float.PolyZonotope` is indexed by ℕ over `Vec`, so a float matrix
polynomial zonotope is a representation to build before this gets a float half.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}

/-- The 0/1 matrix one undirected edge contributes, both orientations at once. -/
def GNN.edgeMat (ij : Fin N × Fin N) : Mat ℝ N N :=
  fun a b => if (a = ij.1 ∧ b = ij.2) ∨ (a = ij.2 ∧ b = ij.1) then 1 else 0

/-- An edge only ever adds to a degree, which is what bounds an uncertain one. -/
theorem GNN.edgeMat_nonneg (ij : Fin N × Fin N) (a b : Fin N) : 0 ≤ GNN.edgeMat ij a b := by
  simp only [GNN.edgeMat]
  split_ifs
  exacts [zero_le_one, le_refl 0]

/-- One edge's weight split into the centre it shifts and the generator it
scales, which is the change of variable in matrix form. -/
theorem GNN.smul_edge_half (t : ℝ) (M : Mat ℝ N N) :
    ((1 + t) / 2 : ℝ) • M = (1/2 : ℝ) • M + t • ((1/2 : ℝ) • M) := by
  rw [smul_smul, ← add_smul]
  congr 1
  ring

/-- The adjacency at one choice of edge weights, which is [1]'s `A(λ)`. -/
def GNN.adjAt (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) : Mat ℝ N N :=
  A + ∑ e, lam e • GNN.edgeMat (U e)


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

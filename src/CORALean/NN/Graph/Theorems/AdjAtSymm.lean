import CORALean.NN.Graph.Uncertain

/-!
# `adjAt` is symmetric when `A` is

Each `edgeMat` writes both orientations of its edge at once
(`aux_edgeMat_symm`), so it is symmetric by construction; `adjAt A U lam =
A + ∑ e, lam e • edgeMat (U e)` is then a sum of symmetric matrices whenever
`A` itself is. This is what lets `[1, §4.3]`'s extra-hop theorems
(`DegreeSubmatrixOfBall`, `MessagePassingSubmatrixOfBall`) apply to
`adjAt A U lam` at all.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `edgeMat` writes both orientations of its edge at once, so it is symmetric. -/
theorem aux_edgeMat_symm (ij : Fin N × Fin N) (a b : Fin N) :
    GNN.edgeMat ij a b = GNN.edgeMat ij b a := by
  have h : ((a = ij.1 ∧ b = ij.2) ∨ (a = ij.2 ∧ b = ij.1)) ↔
      ((b = ij.1 ∧ a = ij.2) ∨ (b = ij.2 ∧ a = ij.1)) := by tauto
  simp only [GNN.edgeMat, h]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `adjAt A U lam` is symmetric whenever `A` is: each `edgeMat` already is. -/
theorem GNN.adjAt_symm (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N) (hSymm : ∀ i j, A i j = A j i)
    (lam : Fin m → ℝ) (i j : Fin N) : GNN.adjAt A U lam i j = GNN.adjAt A U lam j i := by
  simp only [GNN.adjAt, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hSymm i j]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [aux_edgeMat_symm (U e) i j]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

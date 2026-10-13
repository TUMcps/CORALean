module

public import CORALean.NN.Graph.Operations.FloatGcn
public import CORALean.NN.Graph.Operations.GcnLin
public import CORALean.NN.Graph.Theorems.FloatLeftMatMulVec
public import CORALean.NN.Graph.Theorems.FloatRightMatMulVec
public import CORALean.NN.Graph.Theorems.GcnLinApply

@[expose] public section

/-!
# The float graph convolutional layer over-approximates the exact one

[1, Prop. 2] is an equality at the reals; at a float scalar the two `mtimes` round, and the
rounding is in the error box, so what holds is an enclosure: every node-feature matrix `H` whose
stack lies in the input set is mapped by the exact layer `H ↦ P H W`, read at the reals the stored
floats denote, into the output set.

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

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.gcn_outer (P : Mat 𝕋 N N) (W : Mat 𝕋 F₁ F₂) (pZ : PolyZonotope (Vec 𝕋 (N * F₁)))
    (H : Mat ℝ N F₁) (hH : GNN.flatten H ∈ pZ.construct) :
    GNN.flatten (Real.GNN.gcnLin (toRealMat P) (toRealMat W) H)
      ∈ (GNN.gcn P W pZ).construct := by -- --- PROOF ---
  have h1 := PolyZonotope.mtimes_outer (GNN.rightMat N W) pZ ⟨_, hH, rfl⟩
  have h2 := PolyZonotope.mtimes_outer (GNN.leftMat P F₂) _ ⟨_, h1, rfl⟩
  rw [Real.GNN.gcnLin_apply]
  unfold GNN.gcn
  simpa [GNN.rightMat_mulVec, GNN.leftMat_mulVec, Matrix.mul_assoc] using h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

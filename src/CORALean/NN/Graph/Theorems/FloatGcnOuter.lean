module

public import CORALean.NN.Graph.Operations.FloatGcn
public import CORALean.NN.Graph.Operations.GcnLin
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Graph.Theorems.FloatRightMatMulVec
public import CORALean.NN.Graph.Theorems.GcnLinApply

@[expose] public section

/-!
# The float graph convolutional layer over-approximates the exact one

[1, Prop. 2] is an equality at the reals; at a float scalar the two `mtimes` round, and the
rounding is in the error box, so what holds is an enclosure: every node-feature matrix `H` whose
stack lies in the input set is mapped by the exact layer `H ↦ P H W`, read at the reals the stored
floats denote, into the output set.

## Inputs
* `P` – message-passing matrix
* `W` – weight matrix
* `pZ` – stacked node features
* `H` – exact node-feature matrix

## Hypotheses
* `hH` – the features lie in the set

## Conclusion
* the exact layer's output lies in the float layer's set

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F₁ F₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}

/-- `aux_leftMat` reads back as `H ↦ P H`. -/
private theorem GNN.aux_leftMat_mulVec (P : Mat 𝕋 N N) (H : Mat ℝ N F) :
    toRealMat (GNN.aux_leftMat P F) *ᵥ GNN.flatten H = GNN.flatten (toRealMat P * H) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, GNN.flatten, toRealMat, GNN.aux_leftMat, Matrix.mul_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [apply_ite toReal, toReal_zero, Equiv.symm_apply_apply]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.gcn_outer (P : Mat 𝕋 N N) (W : Mat 𝕋 F₁ F₂) (pZ : PolyZonotope (Vec 𝕋 (N * F₁)))
    (H : Mat ℝ N F₁) (hH : GNN.flatten H ∈ pZ.construct) : -- --- CONCL ---
    GNN.flatten (Real.GNN.gcnLin (toRealMat P) (toRealMat W) H)
      ∈ (GNN.gcn P W pZ).construct := by -- --- PROOF ---
  have h1 := PolyZonotope.mtimes_outer (GNN.rightMat N W) pZ ⟨_, hH, rfl⟩
  have h2 := PolyZonotope.mtimes_outer (GNN.aux_leftMat P F₂) _ ⟨_, h1, rfl⟩
  rw [Real.GNN.gcnLin_apply]
  unfold GNN.gcn
  simpa [GNN.rightMat_mulVec, GNN.aux_leftMat_mulVec, Matrix.mul_assoc] using h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

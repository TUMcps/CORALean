module

public import CORALean.NN.Graph.Operations.FloatLinear
public import CORALean.NN.Graph.Operations.Linear
public import CORALean.NN.Graph.Theorems.FloatBiasPointMem
public import CORALean.NN.Graph.Theorems.FloatRightMatMulVec
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# The float graph linear layer over-approximates the exact one

At the reals the layer `H ↦ H Wᵀ + 1 bᵀ` is exact on a polynomial zonotope; at a float scalar the
`mtimes` and the `plus` round, and the rounding is in the error box, so what holds is an
enclosure: every node-feature matrix `H` whose stack lies in the input set is mapped by the exact
layer, read at the reals the stored floats denote, into the output set.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `pZ` – stacked node features
* `H` – exact node-feature matrix

## Hypotheses
* `hH` – the features lie in the set

## Conclusion
* the exact layer's output lies in the float layer's set
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

theorem GNN.linear_outer (W : Mat 𝕋 F₂ F₁) (b : Vec 𝕋 F₂) (pZ : PolyZonotope (Vec 𝕋 (N * F₁)))
    (H : Mat ℝ N F₁) (hH : GNN.flatten H ∈ pZ.construct) :
    GNN.flatten (Real.GNN.linear (toRealMat W) (toRealVec b) H)
      ∈ (GNN.linear W b pZ).construct := by -- --- PROOF ---
  have h1 := PolyZonotope.mtimes_outer (GNN.rightMat N W.transpose) pZ ⟨_, hH, rfl⟩
  beta_reduce at h1
  rw [GNN.rightMat_mulVec] at h1
  exact PolyZonotope.plus_outer _ _
    ⟨_, h1, _, GNN.biasPoint_mem (N := N) b, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

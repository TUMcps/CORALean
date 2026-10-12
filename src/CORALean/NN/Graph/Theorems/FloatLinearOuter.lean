import CORALean.NN.Graph.Operations.FloatLinear
import CORALean.NN.Graph.Operations.Linear
import CORALean.NN.Graph.Theorems.FloatBiasPointMem
import CORALean.NN.Graph.Theorems.FloatRightMatMulVec
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter

/-!
# The float graph linear layer over-approximates the exact one

At the reals the layer `H ↦ H Wᵀ + 1 bᵀ` is exact on a polynomial zonotope; at a float scalar the
`mtimes` and the `plus` round, and the rounding is in the error box, so what holds is an
enclosure: every node-feature matrix `H` whose stack lies in the input set is mapped by the exact
layer, read at the reals the stored floats denote, into the output set.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.linear_outer (W : Mat 𝕋 F₂ F₁) (b : Vec 𝕋 F₂) (pZ : PolyZonotope 𝕋 (N * F₁))
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

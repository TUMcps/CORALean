module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.CentreMemConstruct
public import CORALean.NN.Graph.Operations.FloatBiasPoint
public import CORALean.NN.Graph.Operations.LinearBias

@[expose] public section

/-!
# The bias point contains the bias

The bias row stacked at every node, read at the reals the stored floats denote, lies in
`biasPoint`: it has no generators, so its centre is a member.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.biasPoint_mem (b : Vec 𝕋 F) :
    GNN.flatten (Real.GNN.linearBias N (toRealVec b)) ∈ (GNN.biasPoint N b).construct := by
  have h := PolyZonotope.centre_mem_construct (GNN.biasPoint N b) (fun i => i.elim0)
    (fun i => ⟨le_of_eq (toReal_zero), le_of_eq toReal_zero.symm⟩)
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

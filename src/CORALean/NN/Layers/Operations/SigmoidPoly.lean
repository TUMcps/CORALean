module

public import CORALean.NN.Layers.Operations.ActivationPoly
public import CORALean.NN.Layers.Operations.SigmoidPolyRelaxation

@[expose] public section

/-!
# The polynomial sigmoid layer

That relaxation as a layer, one fit and one grid per neuron: the polynomial activation layer,
built rather than merely stated, every stored field an expression in the scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial activation layer at the sigmoid, one fit and one grid per neuron. -/
def Layer.sigmoidPoly (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    Layer (fun k => Float.PolyZonotope (Vec 𝕋 k)) n n :=
  Layer.activationPoly fun i => sigmoidPolyRelaxation k (c i) (dx i) (p i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

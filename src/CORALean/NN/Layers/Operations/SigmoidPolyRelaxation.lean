module

public import CORALean.NN.Layers.Operations.PolyRelaxationOfSampling
public import CORALean.NN.Layers.Operations.SigmoidPolyDerivBound

@[expose] public section

/-!
# The polynomial relaxation at the sigmoid

`ofSampling` at the sigmoid: `sigmoidEnclosure` is `σ` at a stored value, the derivative bracket
turns into the `M` the sampling bound asks for, and the fit `c` and grid `p`, `dx` stay free —
any array of stored values is a fit, and a grid that fails its check costs precision only.
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

/-- `ofSampling` at the sigmoid, the fit and the grid free. -/
def sigmoidPolyRelaxation (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 m :=
  PolyRelaxation.ofSampling (sigmoidEnclosure k) c (sigmoidPolyDerivBound k c) dx p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

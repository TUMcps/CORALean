import CORALean.NN.Layers.Operations.PolyDerivBoundUp
import CORALean.NN.Layers.Operations.SigmoidDerivHi
import CORALean.NN.Layers.Operations.SigmoidDerivLo
import CORALean.NN.Layers.Operations.SigmoidEnclosure

/-!
# The derivative bound a sampled sigmoid fit asks for

The sigmoid's derivative bracket read against the fit's own, one box at a time.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Sigmoid`'s derivative bracket read against the fit's own. -/
def sigmoidPolyDerivBound (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  polyDerivBoundUp (c l u) (sigmoidDerivLo (sigmoidEnclosure k) l u)
    (sigmoidDerivHi (sigmoidEnclosure k) l u) l u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

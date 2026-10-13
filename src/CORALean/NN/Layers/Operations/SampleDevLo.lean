import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Operations.EvalPolyUp

/-!
# The deviation of σ from a fit at a sample, from below

Over ℝ the sampled value is `σ x - p x`; here neither term is a stored operation, so each is
bracketed and the two subtracted the *crossed* way — the activation's low end against the fit's
high one — which keeps the sampled bracket outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The deviation `σ - p` at one sample, from below. -/
def sampleDevLo (E : Enclosure 𝕋) (c : Fin (m + 1) → 𝕋) (x : 𝕋) : 𝕋 :=
  subDown (E.lo x) (evalPolyUp c x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

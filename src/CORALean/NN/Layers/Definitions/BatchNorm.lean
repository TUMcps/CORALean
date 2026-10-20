module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Batch normalization's statistics, folded

CORA's `nnBatchNormLayer` at inference time is `x i ↦ γ (x i - μ) / √(σ² + ε) + β` per
channel: affine and coordinatewise, so a scale and a shift per channel. Folding the statistics
into them is arithmetic on parameters, done once when a network is read, and at ℝ it is this —
the exact fold `Real.batchNorm_sound` proves the layer against. A network read in floats folds
in floats, and verifies the network its folded numbers describe.

## Inputs
* `gamma` – learned scale
* `var` – running variance
* `eps` – numerical stabiliser

## Output
* scale after folding the statistics into the layer
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def batchNormScale (gamma var eps : ℝ) : ℝ := gamma / Real.sqrt (var + eps)

noncomputable def batchNormShift (gamma beta mean var eps : ℝ) : ℝ :=
  beta - batchNormScale gamma var eps * mean

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

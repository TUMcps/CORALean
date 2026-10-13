import CORALean.NN.Layers.Definitions.Relaxation

/-!
# The tighter of two relaxations

Two relaxations of the same `σ`, the smaller stored error taken on each box. `le` is
unconstrained and does not have to be: both branches are sound, so a wrong answer costs
precision and never soundness.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two relaxations of the same `σ`, the smaller error taken on each box. -/
def Relaxation.tighter (R₁ R₂ : Relaxation 𝕋) : Relaxation 𝕋 where
  slope l u := if le (R₁.error l u) (R₂.error l u) then R₁.slope l u else R₂.slope l u
  offset l u := if le (R₁.error l u) (R₂.error l u) then R₁.offset l u else R₂.offset l u
  error l u := if le (R₁.error l u) (R₂.error l u) then R₁.error l u else R₂.error l u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

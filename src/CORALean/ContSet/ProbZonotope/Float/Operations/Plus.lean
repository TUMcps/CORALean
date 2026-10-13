import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.MatPlus

/-!
# `ProbZonotope.plus`, over a floating-point scalar

`(Z₁ ⊕ Z₂, Σ₁ + Σ₂)`: the float zonotope sum and the interval-matrix sum of the covariances.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.plus (P₁ P₂ : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n :=
  ⟨P₁.Z.plus P₂.Z, Interval.matPlus P₁.cov P₂.cov⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

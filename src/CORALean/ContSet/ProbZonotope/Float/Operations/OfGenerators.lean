import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `ProbZonotope.ofGenerators`, over a floating-point scalar

CORA's `probZonotope(Z, g)`: the mean zonotope `Z` and the covariance `g gᵀ`, as an
interval-matrix product of the point matrices `g` and `gᵀ`.
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

variable {q : ℕ}

def ProbZonotope.ofGenerators (Z : Zonotope (Vec 𝕋 n)) (g : Mat 𝕋 n q) : ProbZonotope 𝕋 n :=
  ⟨Z, Interval.matMul (Interval.point g) (Interval.point g.transpose)⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

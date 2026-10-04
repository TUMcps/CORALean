import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `ProbZonotope.mtimes`, over a floating-point scalar

`(M Z, M Σ Mᵀ)`: the float zonotope image and the interval-matrix product of the covariance with
the point matrices `M` and `Mᵀ`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

variable {m : ℕ}

def ProbZonotope.mtimes (M : Mat 𝕋 m n) (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 m :=
  ⟨Zonotope.mtimes M P.Z,
    Interval.matMul (Interval.matMul (Interval.point M) P.cov) (Interval.point M.transpose)⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

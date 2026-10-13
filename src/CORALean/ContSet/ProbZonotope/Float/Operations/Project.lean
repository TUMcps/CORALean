import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Project

/-!
# `ProbZonotope.project`, over a floating-point scalar

`Z(dims, :)` and `cov(dims, dims)`: the float zonotope projection and the submatrix of the
covariance interval, exact.
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

variable {m : ℕ}

def ProbZonotope.project (P : ProbZonotope 𝕋 n) (dims : Fin m → Fin n) : ProbZonotope 𝕋 m :=
  ⟨P.Z.project dims,
    ⟨fun i j => P.cov.inf (dims i) (dims j), fun i j => P.cov.sup (dims i) (dims j)⟩⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

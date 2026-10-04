import CORALean.ContSet.ProbZonotope.Float.ProbZonotope
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard

/-!
# `ProbZonotope.reduceGirard`, over a floating-point scalar

CORA's `reduce(P, 'girard', o)`: the mean zonotope reduced by `Zonotope.reduceGirard` and the
covariance kept.
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

def ProbZonotope.reduceGirard (P : ProbZonotope 𝕋 n) (o : ℕ) : ProbZonotope 𝕋 n :=
  ⟨P.Z.reduceGirard o, P.cov⟩
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

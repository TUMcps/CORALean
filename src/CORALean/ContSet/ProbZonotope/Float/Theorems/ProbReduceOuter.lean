import CORALean.ContSet.ProbZonotope.Float.Operations.ProbReduce
import CORALean.ContSet.ProbZonotope.Real.Theorems.ProbReduceEq

/-!
# `ProbZonotope.probReduce` keeps the laws

Exact, so outer: every law of `P` is a law of the reduced model, as the real `probReduce` is the
identity on a positive semidefinite covariance (`probReduce_eq`) and the laws of the float model
are those with a positive semidefinite covariance.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.probReduce_laws_outer (P : ProbZonotope 𝕋 n) :
    P.laws ⊆ P.probReduce.laws := fun _ h => h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

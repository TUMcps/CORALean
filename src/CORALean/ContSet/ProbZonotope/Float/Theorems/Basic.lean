module

public import CORALean.ContSet.ProbZonotope.Float.Operations.ProbReduce
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ProbReduceEq

@[expose] public section

/-!
# `ContSet/ProbZonotope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===========================  `ProbZonotope.probReduce_laws_outer`  =========================== --
-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Exact, so outer: every law of `P` is a law of the reduced model, as the real `probReduce` is the
identity on a positive semidefinite covariance (`probReduce_eq`) and the laws of the float model
are those with a positive semidefinite covariance. -/
theorem ProbZonotope.probReduce_laws_outer (P : ProbZonotope 𝕋 n) :
    P.laws ⊆ P.probReduce.laws := fun _ h => h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

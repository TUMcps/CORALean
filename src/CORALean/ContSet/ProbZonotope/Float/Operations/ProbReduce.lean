import CORALean.ContSet.ProbZonotope.Float.ProbZonotope

/-!
# `ProbZonotope.probReduce`, over a floating-point scalar

CORA's `probReduce(probZ)` replaces the probabilistic generators by the `n` generators of the
covariance's eigendecomposition. The model stores the covariance and not the generators, and
the real `probReduce` is the identity on it (`probReduce_eq`), so this is the identity too: the
mean zonotope and the covariance interval are kept.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.probReduce (P : ProbZonotope 𝕋 n) : ProbZonotope 𝕋 n := P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

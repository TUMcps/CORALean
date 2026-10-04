import CORALean.ContSet.ProbZonotope.Real.Operations.Generators
import CORALean.ContSet.ProbZonotope.Real.Operations.OfGenerators

/-!
# `ProbZonotope.probReduce`

CORA's `probReduce(probZ)`: replace the probabilistic generators by the `n` generators
`V √W` of the eigendecomposition of the (symmetrized) covariance. A `ProbZonotope` stores the
covariance only, and the new generators give the covariance `G Gᵀ`
(`ProbZonotope.ofGenerators`); `Theorems.ProbReduceLaws` says this is the same family of laws.
CORA's `gauss` flag, which says whether the covariance or the generators `g` are the master
copy, is not modelled: the covariance always is.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.probReduce (P : ProbZonotope n) : ProbZonotope n :=
  ProbZonotope.ofGenerators P.Z P.generators

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

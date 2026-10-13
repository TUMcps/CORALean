import CORALean.ContSet.ProbZonotope.Real.Operations.ProbReduce
import CORALean.ContSet.ProbZonotope.Real.Theorems.GeneratorsMulTranspose

/-!
# `probReduce` changes the generators, not the probabilistic zonotope

For a positive semidefinite covariance the `n` generators `V √W` give back the covariance
(`generators_mul_transpose`), so `probReduce` is the identity on `ProbZonotope`, which stores
the covariance and not the generators; in particular it keeps the family of laws. What CORA's
`probReduce` changes is the representation: the number of single Gaussians, to the dimension.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.probReduce_eq (P : ProbZonotope n) (h : P.cov.PosSemidef) :
    P.probReduce = P := by
  unfold ProbZonotope.probReduce ProbZonotope.ofGenerators
  rw [P.generators_mul_transpose h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

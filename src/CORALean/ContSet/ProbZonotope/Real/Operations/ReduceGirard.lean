import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

/-!
# `ProbZonotope.reduceGirard`

CORA's `reduce(probZ, 'girard', order)`: the mean zonotope is reduced as a zonotope,
`reduce(zonotope(probZ.Z), 'girard', order)`, and the covariance is kept (CORA's `probReduce`,
for a `probZ` whose `gauss` flag is not set, only reorders the generators of the same
covariance). CORA's second option `'althoff'` ("order set to 1") is not formalized: the zonotope
`reduce` it calls has no such method and throws (FINDINGS.md).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.reduceGirard (P : ProbZonotope n) (o : ℕ) : ProbZonotope n :=
  ⟨P.Z.reduceGirard o, P.cov⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

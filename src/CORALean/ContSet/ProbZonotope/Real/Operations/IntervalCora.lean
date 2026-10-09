import CORALean.ContSet.ProbZonotope.Real.Operations.Generators
import CORALean.ContSet.Interval.Real.Interval

/-!
# `ProbZonotope.intervalCora`

CORA's `interval(probZ)` as the code computes it (`@probZonotope/interval.m`): with
`c = center(probZ)` the first column of `probZ.Z` and `G = generators(probZ)` the eigen factor of
the covariance, the box `c ± Σⱼ |G·ⱼ|`. The deterministic generators `probZ.Z(:,2:end)` are not
read, although the help says it overapproximates the probabilistic zonotope
(`Theorems.IntervalCoraNotMem`). `ProbZonotope.interval` is the box that does.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.intervalCora (P : ProbZonotope n) : Interval (Vec ℝ n) :=
  let c : Vec ℝ n := P.Z.c
  let G : Mat ℝ n n := P.generators
  let leftLimit : Vec ℝ n := c - fun i => ∑ j, |G i j|
  let rightLimit : Vec ℝ n := c + fun i => ∑ j, |G i j|
  ⟨leftLimit, rightLimit⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

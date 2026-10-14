module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Max
public import CORALean.ContSet.Zonotope.Real.Operations.Basic

@[expose] public section

/-!
# `ContSet/ProbZonotope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n m : ℕ}


-- ===================================  `ProbZonotope.mean`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `mean`: the zonotope of possible means, `Z` itself. `Theorems.MeanExact` says it is
exactly the set of the laws' expectations. -/
def ProbZonotope.mean (P : ProbZonotope n) : Zonotope (Vec ℝ n) := P.Z


-- ==================================  `ProbZonotope.project`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `project` (`@probZonotope/project.m`): `Z(dims, :)` and `cov(dims, dims)`, the rows and
the principal submatrix of the selected coordinates. `Theorems.ProjectLaws` says that it maps
the laws by the coordinate projection. -/
def ProbZonotope.project (P : ProbZonotope n) (dims : Fin m → Fin n) : ProbZonotope m :=
  ⟨P.Z.project dims, P.cov.submatrix dims dims⟩


-- ===============================  `ProbZonotope.pyramidLevels`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The array `maxVal` of CORA's `pyramid`: the density `max(probZ, mᵢ)` on the `mᵢ`-sigma bound for
each layer `i`, then the peak `max(probZ, 0)` as `maxVal(end+1)`. -/
noncomputable def ProbZonotope.pyramidLevels (P : ProbZonotope n) {k : ℕ} (mArray : Fin k → ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.snoc (fun i => P.max (mArray i)) (P.max 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
import CORALean.ContSet.Zonotope.Real.Operations.Project

/-!
# `ProbZonotope.project`

CORA's `project` (`@probZonotope/project.m`): `Z(dims, :)` and `cov(dims, dims)`, the rows and
the principal submatrix of the selected coordinates. `Theorems.ProjectLaws` says that it maps
the laws by the coordinate projection.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.project (P : ProbZonotope n) (dims : Fin m → Fin n) : ProbZonotope m :=
  ⟨P.Z.project dims, P.cov.submatrix dims dims⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

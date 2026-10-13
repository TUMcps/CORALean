module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Map

@[expose] public section

/-!
# `Ellipsoid.project`

CORA's `@ellipsoid/project`: the image under the selection matrix, which is how CORA writes it (`P
* E` with `P = I(dims,:)`). `dims` may repeat or reorder coordinates. Reading coordinates is
linear, so this is `map` at the selection map, and `project_exact` is `map_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.project (E : Ellipsoid n)
    (dims : Fin m → Fin n) : Ellipsoid m :=
  E.map (LinearMap.funLeft ℝ ℝ dims)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

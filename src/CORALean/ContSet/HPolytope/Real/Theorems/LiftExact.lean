import CORALean.ContSet.HPolytope.Real.Operations.Lift
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact

/-!
# `HPolytope.lift_` is exactly the preimage under the coordinate selection

A point of the higher-dimensional space is in the lifted polytope exactly when its coordinates
`dims` form a point of `P`; the other coordinates are free.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.lift_exact (P : HPolytope (Vec ℝ n)) (dims : Fin n → Fin N) :
    (P.lift_ dims).construct = {x : Vec ℝ N | (fun k => x (dims k)) ∈ P.construct} :=
  HPolytope.comap_exact (LinearMap.funLeft ℝ ℝ dims) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

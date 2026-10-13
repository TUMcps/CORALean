import CORALean.ContSet.HPolytope.Real.Operations.Lift
import CORALean.ContSet.HPolytope.Real.Operations.Eqs
import CORALean.ContSet.HPolytope.Real.Operations.Intersection
import Mathlib.Data.Finset.Sort

/-!
# `HPolytope.projectHighDim`

CORA's `@polytope/projectHighDim`, the halfspace branch: `lift_` writes the rows into the
coordinates `dims` of the larger space, and one equality `xⱼ = 0` pins every coordinate that
`dims` does not hit, as the lifted polytope would otherwise be unbounded there. The equalities
are `HPolytope.eqs` over the unit rows, in the order of the new coordinates.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P` in the coordinates `dims` of `ℝᴺ`, the other coordinates zero. -/
noncomputable def HPolytope.projectHighDim (P : HPolytope (Vec ℝ n)) (dims : Fin n → Fin N) :
    HPolytope (Vec ℝ N) :=
  open Classical in
  -- the coordinates `dims` leaves out
  let new := Finset.univ.filter fun j => ∀ k, dims k ≠ j
  (P.lift_ dims).intersection
    (HPolytope.eqs (fun r j => if j = (new.orderIsoOfFin rfl r).1 then 1 else 0) 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

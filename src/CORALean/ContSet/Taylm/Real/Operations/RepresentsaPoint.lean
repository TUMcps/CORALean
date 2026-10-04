import CORALean.ContSet.Conversion.Real.Taylm_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaPoint

/-!
# `Taylm.representsa_point`

CORA's `@taylm/representsa`: `pZ = polyZonotope(t)` and then `representsa_(pZ, type, ...)`, so
the answer is the polynomial zonotope's, at the types it covers. `T` is an array of models over
the same variables, as in `Taylm.polyZonotope`. The other types, and the second output
`t_conv`, are not covered.

At `point` the polynomial zonotope's test is sufficient only: every generator is `0`, before
CORA's compaction.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.representsa_point (T : Fin m → Taylm n) : Prop :=
  let pZ := Taylm.polyZonotope T
  pZ.representsa_point


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

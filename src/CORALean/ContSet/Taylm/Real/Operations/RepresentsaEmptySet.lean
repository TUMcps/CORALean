module

public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `Taylm.representsa_emptySet`

CORA's `@taylm/representsa`: `pZ = polyZonotope(t)` and then `representsa_(pZ, type, ...)`, so
the answer is the polynomial zonotope's, at the types it covers. `T` is an array of models over
the same variables, as in `Taylm.polyZonotope`. The other types, and the second output
`t_conv`, are not covered.

At `emptySet` the polynomial zonotope answers `false`: it is never empty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.representsa_emptySet (T : Fin m → Taylm n) : Bool :=
  let pZ := Taylm.polyZonotope T
  pZ.representsa_emptySet


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

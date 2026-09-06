import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.identE`

The identity exponent matrix: factor `i` appears in generator `i` alone and to
the first power, so its monomial is the factor itself — what a free coefficient
looks like once it has been made dependent.

This is the block `dependent` appends, and what a zonotope's generators become
when they are converted into dependent ones. The monomial fact is
`MonomialIdentE.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.identE (m : ℕ) : Fin m → Fin m → ℕ := fun k i => if k = i then 1 else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.abs`, over a floating-point scalar

CORA's `@zonotope/abs.m`: the centre and the generators are replaced by their entrywise absolute
values (`FloatOps.absolute`, a comparison and a sign flip, so exact). The error box is copied.
As at the real layer this is a different set, not an enclosure of the input; the nominal part is
the real `abs` of the input's nominal part (`Zonotope.abs_nominal`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/abs`: `Z.c := abs(Z.c); Z.G := abs(Z.G)`. -/
def Zonotope.abs (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z.h
  c := fun i => absolute (Z.c i)
  G := fun j i => absolute (Z.G j i)
  E := Z.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

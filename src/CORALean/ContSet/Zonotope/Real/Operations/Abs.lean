import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.abs`

CORA's `@zonotope/abs.m`: the zonotope `(|c|, |g₁|, ..., |g_m|)` whose centre and generators are
the entrywise absolute values of the input's. It is a different set, not an enclosure of the
input (see `Zonotope.abs_corner_mem` for what it does keep).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/abs`: `Z.c := abs(Z.c); Z.G := abs(Z.G)`. -/
def Zonotope.abs (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) where
  h := Z.h
  c := fun i => |Z.c i|
  G := fun j i => |Z.G j i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

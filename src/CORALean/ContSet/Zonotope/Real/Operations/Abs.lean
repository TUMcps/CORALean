module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.abs`

CORA's `@zonotope/abs.m`: the zonotope `(|c|, |g₁|, ..., |g_m|)` whose center and generators are
the entrywise absolute values of the input's. It is a different set, not an enclosure of the
input (see `Zonotope.abs_corner_mem` for what it does keep).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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

import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.mtimes`

CORA's `@zonotope/mtimes`: the map applies to centre and generators alike, which
is why a zonotope is closed under it and the generator count is untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

def Zonotope.mtimes (M : Mat ℝ m n) (Z : Zonotope n) : Zonotope m where
  h := Z.h
  c := M *ᵥ Z.c
  G := M * Z.G

end CORALean.Real

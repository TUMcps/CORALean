import CORALean.Real.ContSet.Zonotope.Zonotope

/-!
# `Zonotope.plus`

CORA's `@zonotope/plus`: centres add, generators concatenate.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Zonotope.plus (Z₁ Z₂ : Zonotope n) : Zonotope n where
  h := Z₁.h + Z₂.h
  c := Z₁.c + Z₂.c
  G := fun i => Fin.append (Z₁.G i) (Z₂.G i)

end CORALean.Real

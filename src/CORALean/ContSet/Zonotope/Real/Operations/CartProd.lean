import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.Module.Prod

/-!
# `Zonotope.cartProd`

CORA's `@zonotope/cartProd_`: the centres pair, `c = [c1; c2]`, and the generator matrix is
`blkdiag(G1, G2)`. Here every generator embeds into the product ambient type at zero in the
other coordinate, as `ConPolyZono.cartProd` does; at `Vec` the product is `blkdiag`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cartProd (Z₁ : Zonotope α) (Z₂ : Zonotope β) : Zonotope (α × β) where
  h := Z₁.h + Z₂.h
  c := (Z₁.c, Z₂.c)
  G := Fin.append (fun j => (Z₁.G j, (0 : β))) (fun j => ((0 : α), Z₂.G j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

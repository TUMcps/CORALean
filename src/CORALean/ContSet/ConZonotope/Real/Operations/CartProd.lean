module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import Mathlib.Algebra.Module.Prod

@[expose] public section

/-!
# `ConZonotope.cartProd`

CORA's `@conZonotope/cartProd_`: centers pair, generators are block-diagonal, and the
constraints stack block-diagonally. As for `plus`, each half of the concatenated coefficient
vector answers only to its own polytope, so the constraints are `comap` and `intersection`;
every generator embeds into the product ambient type at zero in the other coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.cartProd (cZ₁ : ConZonotope α) (cZ₂ : ConZonotope β) : ConZonotope (α × β) where
  h := cZ₁.h + cZ₂.h
  c := (cZ₁.c, cZ₂.c)
  G := Fin.append (fun j => (cZ₁.G j, (0 : β))) (fun j => ((0 : α), cZ₂.G j))
  P := (cZ₁.P.comap (blockLeft cZ₁.h cZ₂.h)).intersection (cZ₂.P.comap (blockRight cZ₁.h cZ₂.h))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

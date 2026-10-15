module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyZonotope.cartProd`

CORA's `@polyZonotope/cartProd`: the centers pair, and every generator embeds
into the product ambient type at zero in the other coordinate, rather than
concatenating within one ambient type the way `plus` does — the two operands
no longer share an ambient type, so there is nothing to add.

The exponent matrices still lay out block-diagonally, exactly as `plus`'s do:
`plusE` is agnostic to what a generator denotes, and here too neither set's
factors may reach the other's generators.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cartProd (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    PolyZonotope (α × β) where
  p := pZ₁.p + pZ₂.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := (pZ₁.c, pZ₂.c)
  G := Fin.append (fun i => (pZ₁.G i, (0 : β))) (fun i => ((0 : α), pZ₂.G i))
  E := PolyZonotope.plusE pZ₁.E pZ₂.E
  GI := Fin.append (fun j => (pZ₁.GI j, (0 : β))) (fun j => ((0 : α), pZ₂.GI j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

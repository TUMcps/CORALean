module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.point`

The point a factor vector picks out, the independent block left aside;
`construct` is the image of this map, widened by that block.

It is what a product of two polynomial zonotopes is stated against. Both sets
are functions of the *same* factors, so the exact claim is about
`a ↦ point pZ₁ a ⊙ point pZ₂ a` and not about the product of the two sets, which
is generally far larger.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The point the factor vector `a` picks out, the independent block aside. -/
def PolyZonotope.point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) : α :=
  pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

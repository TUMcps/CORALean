import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.point`

The point a factor vector picks out, the independent block left aside;
`construct` is the image of this map, widened by that block.

It is what a product of two polynomial zonotopes is stated against. Both sets
are functions of the *same* factors, so the exact claim is about
`a ↦ point S₁ a ⊙ point S₂ a` and not about the product of the two sets, which
is generally far larger.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The point the factor vector `a` picks out, the independent block aside. -/
def PolyZonotope.point (S : PolyZonotope α) (a : Fin S.p → ℝ) : α :=
  S.c + ∑ i, PolyZonotope.monomial S.E a i • S.G i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

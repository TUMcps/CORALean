module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.affine`

The map onto the set, affine in the independent half and polynomial in the
dependent one.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The map onto the set, affine in the independent half and polynomial in the
dependent one. -/
def ConPolyZono.affine (cPZ : ConPolyZono α) (ab : (Fin cPZ.p → ℝ) × (Fin cPZ.q → ℝ)) : α :=
  cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E ab.1 i • cPZ.G i + ∑ j, ab.2 j • cPZ.GI j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

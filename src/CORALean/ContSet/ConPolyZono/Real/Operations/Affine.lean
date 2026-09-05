import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.affine`

The map onto the set, affine in the independent half and polynomial in the
dependent one.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The map onto the set, affine in the independent half and polynomial in the
dependent one. -/
def ConPolyZono.affine (C : ConPolyZono α) (ab : (Fin C.p → ℝ) × (Fin C.q → ℝ)) : α :=
  C.c + ∑ i, PolyZonotope.monomial C.E ab.1 i • C.G i + ∑ j, ab.2 j • C.GI j

end CORALean.Real

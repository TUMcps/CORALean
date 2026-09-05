import CORALean.ContSet.ConPolyZono.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConPolyZono.Real.Theorems.ContinuousAffine
import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompactDomain

/-!
# A constrained polynomial zonotope is compact

The continuous image of a compact domain. Not convex, and not closed for any
reason a zonotope is closed — the set is a polynomial image of a cube cut by
polynomial constraints — but compact all the same, which is what an algorithm
enclosing an integral asks for.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem ConPolyZono.isCompact_construct (C : ConPolyZono α) : IsCompact C.construct := by
  rw [ConPolyZono.construct_eq_image]
  exact C.isCompact_domain.image C.continuous_affine

end CORALean.Real

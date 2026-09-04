import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine

/-!
# A constrained zonotope is compact

The image of `domain` under the same affine map a zonotope uses. The domain is
compact, and a continuous image of a compact set is compact.

Stated at `Vec`, unlike the zonotope's: it is the coefficient space that has to
be finite-dimensional, and `HPolytope.isClosed_construct` asks for that.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

theorem ConZonotope.isCompact_construct (C : ConZonotope α) : IsCompact C.construct := by
  rw [ConZonotope.construct_eq_image]
  exact C.isCompact_domain.image (Zonotope.continuous_affine C.zonotope)

end CORALean.Real

import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

/-!
# A constrained zonotope is compact, hence closed

The image of `domain` under the same affine map a zonotope uses. The domain is
closed because it is a polytope, and bounded because it sits in the coefficient
cube, so it is compact and the image is too.

Stated at `Vec`, unlike the zonotope's: it is the coefficient space that has to
be finite-dimensional, and `HPolytope.isClosed_construct` asks for that.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

omit [NormedAddCommGroup α] [NormedSpace ℝ α] in
theorem ConZonotope.isCompact_domain (C : ConZonotope α) : IsCompact C.domain.construct := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall 0 1)
    (HPolytope.isClosed_construct C.domain) fun β hβ => ?_
  rw [Zonotope.closedBall_eq]
  exact (ConZonotope.mem_domain_iff.mp hβ).1

theorem ConZonotope.isCompact_construct (C : ConZonotope α) : IsCompact C.construct := by
  rw [ConZonotope.construct_eq_image]
  exact C.isCompact_domain.image (Zonotope.continuous_affine C.zonotope)

theorem ConZonotope.isClosed_construct (C : ConZonotope α) : IsClosed C.construct :=
  C.isCompact_construct.isClosed

theorem ConZonotope.isBounded_construct (C : ConZonotope α) :
    Bornology.IsBounded C.construct :=
  C.isCompact_construct.isBounded

end CORALean.Real

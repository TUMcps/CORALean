module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine

@[expose] public section

/-!
# A constrained zonotope is compact

The image of `domain` under the same affine map a zonotope uses. The domain is
compact, and a continuous image of a compact set is compact.

Stated at `Vec`, unlike the zonotope's: it is the coefficient space that has to
be finite-dimensional, and `HPolytope.isClosed_construct` asks for that.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isCompact_construct (cZ : ConZonotope α) : IsCompact cZ.construct := by
  rw [ConZonotope.construct_eq_image]
  exact cZ.isCompact_domain.image (Zonotope.continuous_affine cZ.zonotope)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

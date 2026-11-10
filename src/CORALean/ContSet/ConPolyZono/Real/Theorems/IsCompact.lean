module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.ToSetEqImage
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ContinuousAffine
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompactDomain

@[expose] public section

/-!
# A constrained polynomial zonotope is compact

The continuous image of a compact domain. Not convex, and not closed for any
reason a zonotope is closed — the set is a polynomial image of a cube cut by
polynomial constraints — but compact all the same, which is what an algorithm
enclosing an integral asks for.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is compact
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isCompact_toSet (cPZ : ConPolyZono α) : IsCompact cPZ.toSet := by
  rw [ConPolyZono.toSet_eq_image]
  exact cPZ.isCompact_domain.image cPZ.continuous_affine

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

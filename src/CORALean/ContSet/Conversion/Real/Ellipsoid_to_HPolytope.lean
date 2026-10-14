module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_HPolytope

@[expose] public section

/-!
# An ellipsoid as halfspaces

Through the zonotope: a direct minimum-facet halfspace description of an
ellipsoid is a separate piece of mathematics, and CORA's `polytope(ellipsoid)`
is not this composition. This is what closes the pair for now.

Loses whatever the zonotope step lost and nothing further; exact only on the
directions the caller names, as `Zonotope.hPolytope_contains` already is.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.hPolytope_contains (E : Ellipsoid n) (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    E.construct ⊆ (E.hPolytope Aq).construct :=
  subset_trans E.zonotope_contains (Zonotope.hPolytope_contains _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

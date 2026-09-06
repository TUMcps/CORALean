import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope

/-!
# An ellipsoid as halfspaces

Through the zonotope: a direct minimum-facet halfspace description of an
ellipsoid is a separate piece of mathematics, and CORA's `polytope(ellipsoid)`
is not this composition. This is what closes the pair for now.

Loses whatever the zonotope step lost and nothing further; exact only on the
directions the caller names, as `Zonotope.subset_hPolytope` already is.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q : ℕ}

noncomputable def Ellipsoid.hPolytope (E : Ellipsoid n) (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    HPolytope (Vec ℝ n) :=
  E.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.subset_hPolytope (E : Ellipsoid n) (Aq : Fin q → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    E.construct ⊆ (E.hPolytope Aq).construct :=
  subset_trans E.zonotope_outer (Zonotope.subset_hPolytope _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

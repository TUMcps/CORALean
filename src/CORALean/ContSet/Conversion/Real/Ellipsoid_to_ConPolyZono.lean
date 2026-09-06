import CORALean.ContSet.Conversion.Real.Ellipsoid_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

/-!
# An ellipsoid as a constrained polynomial zonotope

Through the box the ellipsoid gives, then that box's zonotope, then the
zonotope's exact reading as a polynomial zonotope, then `PolyZonotope.conPolyZono`
— an empty constraint system, so that last leg adds nothing and is exact. All the
loss is the box route's, exactly as in `Ellipsoid.subset_polyZonotope`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.conPolyZono (E : Ellipsoid n) : ConPolyZono (Vec ℝ n) :=
  E.polyZonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.subset_conPolyZono (E : Ellipsoid n) :
    E.construct ⊆ E.conPolyZono.construct :=
  subset_trans E.subset_polyZonotope (PolyZonotope.conPolyZono_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeEllipsoidContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A bundle's ellipsoid, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own ball, loose by a
factor of `√h` in the worst direction. Whichever component `i` names already
throws away every other one the bundle intersects against — the whole point of
a bundle being that the intersection is tighter than any one member — so the
loss compounds with the zonotope step's.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.ellipsoid_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.ellipsoid i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

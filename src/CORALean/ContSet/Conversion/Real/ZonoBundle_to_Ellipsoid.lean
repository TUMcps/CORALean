import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

/-!
# A bundle's ellipsoid, at one component

Through `ZonoBundle.zonotope i`, then that zonotope's own ball, loose by a
factor of `√h` in the worst direction. Whichever component `i` names already
throws away every other one the bundle intersects against — the whole point of
a bundle being that the intersection is tighter than any one member — so the
loss compounds with the zonotope step's.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def ZonoBundle.ellipsoid (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) : Ellipsoid n :=
  (zB.zonotope i).ellipsoid


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.ellipsoid_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.ellipsoid i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.ellipsoid_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import Mathlib.Order.BourbakiWitt

/-!
# A bundle's box, at one component

Through `ZonoBundle.zonotope i`: the choice of component is free, and it already
throws away every other one the bundle intersects against — the whole point of
a bundle being that the intersection is tighter than any one member. The box
step then loses nothing further.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

def ZonoBundle.interval (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) : Interval (Vec ℝ n) :=
  (zB.zonotope i).interval


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.interval_contains (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.interval i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.interval_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

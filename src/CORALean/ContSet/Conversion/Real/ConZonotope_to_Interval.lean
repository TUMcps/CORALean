import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval

/-!
# A constrained zonotope as a box

Constraints dropped, then the zonotope's own box. Cheap and loose: the tight box
is `2n` linear programs on the coefficient domain, which `HPolytope.interval`
does once a caller has the certificates for it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

def ConZonotope.interval (cZ : ConZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  cZ.zonotope.interval


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.interval_contains (cZ : ConZonotope (Vec ℝ n)) :
    cZ.construct ⊆ cZ.interval.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.interval_contains _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

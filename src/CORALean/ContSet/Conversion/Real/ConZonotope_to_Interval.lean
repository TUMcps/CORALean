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

def ConZonotope.interval (C : ConZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  C.zonotope.interval


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.interval_outer (C : ConZonotope (Vec ℝ n)) :
    C.construct ⊆ C.interval.construct :=
  subset_trans C.zonotope_outer (Zonotope.interval_outer _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

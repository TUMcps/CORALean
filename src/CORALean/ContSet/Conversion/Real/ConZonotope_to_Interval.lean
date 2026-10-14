module

public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_Interval

@[expose] public section

/-!
# A constrained zonotope as a box

Constraints dropped, then the zonotope's own box. Cheap and loose: the tight box
is `2n` linear programs on the coefficient domain, which `HPolytope.interval`
does once a caller has the certificates for it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.interval_contains (cZ : ConZonotope (Vec ℝ n)) :
    cZ.construct ⊆ cZ.interval.construct :=
  subset_trans cZ.zonotope_contains (Zonotope.interval_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

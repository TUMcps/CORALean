module

public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_StarSet
public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# A constrained zonotope as a star set

CORA's `conversionConZonoStarSet`: the center and the generators as they are, the factors in
`[-1, 1]`, and the rows of the constraint polytope on the factors as the constraint rows.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.starSet (cZ : ConZonotope (Vec ℝ n)) : StarSet StarSet.LinPred n where
  m := cZ.h
  c := cZ.c
  G := fun i k => cZ.G k i
  pred := ⟨cZ.P.starRows, fun _ => -1, fun _ => 1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

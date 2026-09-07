import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Real.Operations.RadiusReach

/-!
# `ConZonotope.mtimesIntervalMat`

The zonotope operation with the constraints carried along: the centre acts
exactly and the radius is boxed into one fresh generator per coordinate, exactly
as for a zonotope. The constraints are pulled back along the projection onto the
original coefficients, which is what says the fresh ones answer to nothing.

`radiusReach` is read off the enclosing zonotope. Using the constraints to
tighten it is possible and is not done: the bound only has to hold, and a looser
one keeps this an enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ConZonotope.mtimesIntervalMat (IM : Interval (Mat ℝ m n))
    (cZ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ m) where
  h := cZ.h + m
  c := IM.center *ᵥ cZ.c
  G := Fin.append (fun l => IM.center *ᵥ cZ.G l)
        (Matrix.diagonal fun i => Zonotope.radiusReach IM cZ.zonotope i)
  P := cZ.P.comap (blockLeft cZ.h m)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

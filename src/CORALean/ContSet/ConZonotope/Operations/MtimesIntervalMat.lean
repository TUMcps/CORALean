import CORALean.ContSet.ConZonotope.Operations.Zonotope

/-!
# `ConZonotope.mtimesIntervalMat`

The zonotope operation with the constraints carried along: the centre acts
exactly and the radius is boxed into one fresh generator per coordinate, exactly
as for a zonotope, and the constraint block is padded with a zero column per
fresh generator — those coefficients answer to nothing.

`radiusReach` is read off the enclosing zonotope. Using the constraints to
tighten it is possible and is not done: the bound only has to hold, and a looser
one keeps this an enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {m n : ℕ}

noncomputable def ConZonotope.mtimesIntervalMat (IM : Interval (Mat ℝ m n))
    (C : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ m) where
  h := C.h + m
  q := C.q
  c := IM.center *ᵥ C.c
  G := Fin.append (fun l => IM.center *ᵥ C.G l)
        (Matrix.diagonal fun i => Zonotope.radiusReach IM C.zonotope i)
  A := fun i => Fin.append (C.A i) 0
  b := C.b

end CORALean.Real

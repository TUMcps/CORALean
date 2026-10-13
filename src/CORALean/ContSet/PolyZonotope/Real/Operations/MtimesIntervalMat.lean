import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.PolyZonotope.Real.Operations.RadiusReach
import Mathlib.Data.Matrix.Mul

/-!
# Polynomial zonotopes: multiplication by an interval matrix

CORA writes this as `mtimes` too, dispatching on the argument. The centre acts
exactly on every block. Everything the radius allows is boxed into one fresh
generator per coordinate, and it goes into the *independent* block: the
matrix's uncertainty answers to none of the set's dependent factors, so making
it dependent would misstate where the sharing is.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.mtimesIntervalMat (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) : PolyZonotope (Vec ℝ m) where
  p := pZ.p
  h := pZ.h
  q := pZ.q + m
  c := IM.center *ᵥ pZ.c
  G := fun i => IM.center *ᵥ pZ.G i
  E := pZ.E
  GI := Fin.append (fun j => IM.center *ᵥ pZ.GI j)
        (Matrix.diagonal fun i => PolyZonotope.radiusReach IM pZ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

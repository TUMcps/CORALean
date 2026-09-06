import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.PolyZonotope.Real.Operations.RadiusReach

/-!
# Polynomial zonotopes: multiplication by an interval matrix

CORA writes this as `mtimes` too, dispatching on the argument. The centre acts
exactly on every block. Everything the radius allows is boxed into one fresh
generator per coordinate, and it goes into the *independent* block: the
matrix's uncertainty answers to none of the set's dependent factors, so making
it dependent would misstate where the sharing is.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.mtimesIntervalMat (IM : Interval (Mat ℝ m n))
    (PZ : PolyZonotope (Vec ℝ n)) : PolyZonotope (Vec ℝ m) where
  p := PZ.p
  h := PZ.h
  q := PZ.q + m
  c := IM.center *ᵥ PZ.c
  G := fun i => IM.center *ᵥ PZ.G i
  E := PZ.E
  GI := Fin.append (fun j => IM.center *ᵥ PZ.GI j)
        (Matrix.diagonal fun i => PolyZonotope.radiusReach IM PZ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

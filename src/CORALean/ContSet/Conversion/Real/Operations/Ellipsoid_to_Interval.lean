module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Theorems.SubsetOfBounds

@[expose] public section

/-!
# An ellipsoid as a box

## Inputs
* `E` – ellipsoid

## Output
* interval of per-coordinate extents of the ellipsoid
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.interval (E : Ellipsoid n) : Interval (Vec ℝ n) :=
  Interval.ofBounds (fun j => E.supportBound (LinearMap.proj j))
    (fun j => E.supportBound (-LinearMap.proj j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

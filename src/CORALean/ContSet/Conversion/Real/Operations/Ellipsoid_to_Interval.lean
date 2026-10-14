module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds

@[expose] public section

/-!
# An ellipsoid as a box — the construction

`Ellipsoid.interval` is the construction; `Ellipsoid_to_Interval` states and proves what it
guarantees.
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

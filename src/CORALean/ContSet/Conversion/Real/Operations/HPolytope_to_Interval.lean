module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Interval.Real.Operations.OfBounds
public import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds

@[expose] public section

/-!
# A halfspace description as a box — the construction

`HPolytope.interval` is the construction; `HPolytope_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.interval (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : Interval (Vec ℝ n) :=
  Interval.ofBounds up lo

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Interval.Real.Operations.Intersection
import CORALean.Global.Cost

/-!
# `Interval.intersectionCost`

Asserted, not proved: `Operations/Intersection.lean` takes a `max` of the two
lower bounds and a `min` of the two upper bounds entrywise, one comparison
each, so at `Vec ℝ n` it is `2 * n` comparisons and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.intersection` costs at `Vec ℝ n`: one comparison per entry
of `inf` and one per entry of `sup`. -/
def Interval.intersectionCost (n : ℕ) : Cost := ⟨2 * n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

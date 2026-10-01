import CORALean.ContSet.Interval.Real.Operations.Times
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# `Interval.times` contains the entrywise products

Each coordinate is `mul_between_corners`. No hypothesis: it is an inclusion.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.times_outer (I J : Interval (Vec ℝ n)) :
    Set.image2 (fun x y i => x i * y i) I.construct J.construct ⊆ (I.times J).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩ i
  exact Interval.mul_between_corners (hx i).1 (hx i).2 (hy i).1 (hy i).2


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

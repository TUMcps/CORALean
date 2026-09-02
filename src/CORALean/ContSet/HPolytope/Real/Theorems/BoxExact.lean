import CORALean.ContSet.HPolytope.Real.Operations.Box

/-!
# `HPolytope.box` is exactly the interval

Both sides read the same two bounds off each coordinate; only the shape of the
statement differs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem HPolytope.box_exact (I : Interval (Vec ℝ n)) :
    (HPolytope.box I).construct = I.construct := by
  ext x
  constructor
  · intro hx i
    exact HPolytope.mem_box_iff.mp hx i
  · intro hx
    exact HPolytope.mem_box_iff.mpr fun i => hx i

end CORALean.Real

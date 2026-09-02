import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.Corners

/-!
# `VPolytope.ofInterval`

A box as its `2ⁿ` corners. Exponential, and inherently so: a box in `n`
dimensions has that many vertices and a vertex description has to name them all.
It is nevertheless the primitive the other direction of the polytope conversion
rests on — a halfspace description becomes vertices by first becoming a box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The corner that takes each coordinate's upper end where `σ` says so. -/
def boxCorner (I : Interval (Vec ℝ n)) (σ : Fin n → Bool) : Vec ℝ n :=
  fun j => if σ j then I.sup j else I.inf j

noncomputable def VPolytope.ofInterval (I : Interval (Vec ℝ n)) : VPolytope (Vec ℝ n) where
  k := 2 ^ n
  V := fun l => boxCorner I (signEquiv n l)

end CORALean.Real

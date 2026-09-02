import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.Interval.Real.Interval

/-!
# `VPolytope.interval`

CORA's `interval(polytope)`: the smallest box holding every vertex, which is the
smallest box holding their hull — a combination of points never leaves a box all
of them are in.

With no vertices the bounds are whatever `⨅` and `⨆` give over an empty index,
which is sound however it lands: the polytope is `∅` then, and `∅` sits inside
any box.

At `Vec` only, a box being read coordinatewise.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.interval (P : VPolytope (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => ⨅ l, P.V l i
  sup := fun i => ⨆ l, P.V l i

end CORALean.Real

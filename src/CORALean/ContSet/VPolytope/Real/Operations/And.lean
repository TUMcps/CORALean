import CORALean.ContSet.VPolytope.Real.Operations.OfInterval
import CORALean.ContSet.VPolytope.Real.Operations.Interval
import CORALean.ContSet.Interval.Real.Operations.And

/-!
# `VPolytope.and`

Intersection, which is the one operation vertices are bad at: the intersection's
vertices are generally none of either operand's, and finding them is facet
enumeration on both sides followed by vertex enumeration on the result.

So this goes through boxes — each polytope's own box, intersected, back to
corners. Sound, exponential in the dimension rather than in the vertex counts,
and loose: the answer is a box, and everything the two hulls did not fill is
kept. Exact when both operands were boxes to begin with.

A tighter version needs the conversion `Polytope` does not have, and would be an
algorithm rather than a definition.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.and (P₁ P₂ : VPolytope (Vec ℝ n)) : VPolytope (Vec ℝ n) :=
  VPolytope.ofInterval (P₁.interval.and P₂.interval)

end CORALean.Real

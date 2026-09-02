import CORALean.ContSet.VPolytope.Real.Operations.Interval
import CORALean.ContSet.VPolytope.Real.Operations.SupportBound

/-!
# `VPolytope.interval` contains the polytope

Coordinatewise, and the same argument at both ends, which is
`le_of_forall_le` at `±eⱼ`: a convex combination of values each below the
supremum is below it too.

Nothing here needs the vertex set to be nonempty — at no vertices the weights
cannot sum to one, so there is nothing to bound.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem VPolytope.interval_outer (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.interval.construct := by
  intro x hx i
  have hbddA : BddAbove (Set.range fun l => P.V l i) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range fun l => P.V l i) := (Set.finite_range _).bddBelow
  constructor
  · -- the lower bound as an upper bound in direction `-eᵢ`, which is the form
    -- `le_of_forall_le` takes
    have h : -(x i) ≤ -(⨅ l, P.V l i) :=
      P.le_of_forall_le (-LinearMap.proj i) (fun l => neg_le_neg (ciInf_le hbddB l)) hx
    show (⨅ l, P.V l i) ≤ x i
    linarith
  · exact P.le_of_forall_le (LinearMap.proj i) (fun l => le_ciSup hbddA l) hx

end CORALean.Real

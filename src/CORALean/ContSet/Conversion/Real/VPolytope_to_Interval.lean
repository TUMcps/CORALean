import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.Interval.Real.Interval

/-!
# A hull as a box

CORA's `interval(polytope)` on a vertex description: the smallest box holding
every vertex, which is the smallest box holding their hull — a combination of
points never leaves a box all of them are in.

With no vertices the bounds are whatever `⨅` and `⨆` give over an empty index,
which is sound however it lands: the polytope is `∅` then, and `∅` sits inside
any box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.interval (P : VPolytope (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => ⨅ l, P.V l i
  sup := fun i => ⨆ l, P.V l i


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.interval_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.interval.construct := by -- --- PROOF ---
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
public import CORALean.ContSet.ContSet.Operations.Enclose

@[expose] public section

/-!
# `enclose` of V-polytopes is exactly the convex hull

At ℝ the generic `ContSet.enclose` of vertex lists is `linComb` (the vertex lists appended, which is
`convHull`) of `P` and `M P + Q`, and `mtimes` and `plus` are exact, so the result is exactly the
convex hull of `P` and `M P + Q`, as CORA's `enclose` computes it.

Not collected in `Theorems/API.lean`: it needs the instances, which that API feeds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.enclose_exact (P Q : VPolytope (Vec ℝ n)) (M : Mat ℝ n n) :
    ContSet.construct (ContSet.enclose (S := fun n => VPolytope (Vec ℝ n)) P M Q) =
      convexHull ℝ (P.construct ∪ ((fun x => M.mulVec x) '' P.construct + Q.construct)) := by
  show (VPolytope.convHull P (VPolytope.plus (VPolytope.mtimes M P) Q)).construct = _
  rw [VPolytope.convHull_exact, ← VPolytope.plus_exact, ← VPolytope.mtimes_exact]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

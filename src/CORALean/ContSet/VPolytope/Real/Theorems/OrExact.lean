module

public import CORALean.ContSet.VPolytope.Real.Operations.Or
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact

@[expose] public section

/-!
# `VPolytope.or` is exactly the convex hull of the union

The union of two polytopes is not a polytope in general, so `or` returns its hull; that hull is
exact, and contains the union.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.or_exact {α : Type} [AddCommGroup α] [Module ℝ α] (P Q : VPolytope α) :
    (P.or Q).construct = convexHull ℝ (P.construct ∪ Q.construct) :=
  VPolytope.convHull_exact P Q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

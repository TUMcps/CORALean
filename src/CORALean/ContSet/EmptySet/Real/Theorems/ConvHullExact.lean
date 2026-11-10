module

public import CORALean.ContSet.EmptySet.Real.Operations.Basic
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.convHull` is the convex hull

Exact for a convex operand, which is every `ConvexSet`.

## Inputs
* `S` – type of the convex set
* `E` – empty set
* `s` – convex set

## Hypotheses
* none

## Conclusion
* `convHull` is the convex hull of the union
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet ContSetLike

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.convHull_exact {S : Type} [ContSetLike S (Vec ℝ n)] [ConvexSet S (Vec ℝ n)]
    (E : EmptySet n) (s : S) :
    convexHull ℝ (E.toSet ∪ ContSetLike.toSet s) = ContSetLike.toSet (E.convHull s) := by
  change convexHull ℝ ((∅ : Set (Vec ℝ n)) ∪ ContSetLike.toSet s) = ContSetLike.toSet s
  rw [Set.empty_union]
  exact (ConvexSet.convex_toSet s).convexHull_eq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

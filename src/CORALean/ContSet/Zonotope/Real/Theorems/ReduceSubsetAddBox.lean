module

public import CORALean.ContSet.Zonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox

@[expose] public section

/-!
# Reduction reaches no further than the original plus its own box, at `reduce`

`reduceBy_subset_add_box` lifted to the operation the `Reduce` instance runs, which is what a step
of `LinearSysDT.reach` calls. `reduceBox` splits on the same condition `reduceGirard` does, so the
two branches come apart together. Above the order the partition is the same on both sides and
`reduceBy_subset_add_box` closes it. At or below it nothing is dropped, the box is the origin, and
the inclusion is `x = x + 0` — the branch a statement at `reduceBy` alone never answers for.
`_subset_` rather than `_outer`: this is not the guarantee `Reduce` asks for, which runs the other
way, but a bound on how far the reduction moved, and no class states that.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the reduction lies in `Z` plus the box
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reduced zonotope lies inside the original plus the box the reduction
introduced — at every order, the no-op branch included. -/
theorem Zonotope.reduce_subset_add_box (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    (Z.reduce o).construct ⊆ Z.construct + (Z.reduceBox o).construct := by -- --- PROOF ---
  unfold Zonotope.reduce Zonotope.reduceGirard Zonotope.reduceBox
  split_ifs with hlt
  · exact Z.reduceBy_subset_add_box _
  -- nothing dropped: the box is the origin, and every point is itself plus `0`
  · intro x hx
    have h := Set.add_mem_add hx (Zonotope.mem_ofPoint (0 : Vec ℝ n))
    rwa [add_zero] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

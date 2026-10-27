module

public import CORALean.ContSet.Zonotope.Real.Definitions.WalkEdges
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The walk edges, spelt in sign corners

`walkEdges` is the union over `k` of `[corner (j < k); corner (j < k + 1)]` and the mirrored
`[corner (¬ j < k); corner (¬ j < k + 1)]`: the walk's two blocks read off `Fin.append`, the
edges `[P; P + 2g]` that [1, Alg. 3] scans in its two loops.

## Inputs
* `Z` – zonotope
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` is on the walk edges iff it lies on one of the segments

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_walkEdges_iff (Z : Zonotope α) (x : α) : -- --- CONCL ---
    x ∈ Z.walkEdges ↔ ∃ k : Fin Z.h,
      x ∈ segment ℝ (Z.corner fun j => decide (j.val < k.val))
          (Z.corner fun j => decide (j.val < k.val + 1)) ∨
      x ∈ segment ℝ (Z.corner fun j => !decide (j.val < k.val))
          (Z.corner fun j => !decide (j.val < k.val + 1)) := by -- --- PROOF ---
  simp only [Zonotope.walkEdges, Set.mem_iUnion, Set.mem_union, Zonotope.walk,
    Fin.append_left, Fin.append_right, Fin.val_castSucc, Fin.val_succ]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

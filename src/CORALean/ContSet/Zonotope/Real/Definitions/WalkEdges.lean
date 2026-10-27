module

public import CORALean.ContSet.Zonotope.Real.Operations.Walk
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

/-!
# The edges of the walk of a zonogon

The segments between consecutive corners of `Zonotope.walk`: `[W_k; W_{k+1}]` along the first
block, `c - Σ g + 2 Σ_{j<k} g`, and the same along the second, mirrored through the center. These
are the segments `[P; P + 2g]` of [1, Sec. 3.2 (zonogons)] that [1, Alg. 3] scans in its two
loops; for generators in the upper half-plane sorted by angle they make up the boundary of the
zonogon.

## Inputs
* `Z` – zonotope

## Output
* edges between consecutive corners of the walk

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The segments joining consecutive corners of the walk, in both blocks: the edges the scan of
[1] visits. -/
def Zonotope.walkEdges (Z : Zonotope α) : Set α :=
  ⋃ k : Fin Z.h,
    segment ℝ (Z.walk (Fin.castAdd _ k.castSucc)) (Z.walk (Fin.castAdd _ k.succ)) ∪
      segment ℝ (Z.walk (Fin.natAdd _ k.castSucc)) (Z.walk (Fin.natAdd _ k.succ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

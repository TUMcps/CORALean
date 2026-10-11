import CORALean.ContSet.Zonotope.Real.Operations.Walk
import Mathlib.Analysis.Convex.Segment

/-!
# The edges of the walk of a zonogon

The segments between consecutive corners of `Zonotope.walk`: `[W_k; W_{k+1}]` along the first
block, `c - Σ g + 2 Σ_{j<k} g`, and the same along the second, mirrored through the centre. These
are the segments `[P; P + 2g]` of [1, Sec. 3.2 (zonogons)] that [1, Alg. 3] scans in its two
loops; for generators in the upper half-plane sorted by angle they make up the boundary of the
zonogon.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the segments joining consecutive corners of the walk, in both blocks. -/
def Zonotope.walkEdges (Z : Zonotope α) : Set α :=
  ⋃ k : Fin Z.h,
    segment ℝ (Z.walk (Fin.castAdd _ k.castSucc)) (Z.walk (Fin.castAdd _ k.succ)) ∪
      segment ℝ (Z.walk (Fin.natAdd _ k.castSucc)) (Z.walk (Fin.natAdd _ k.succ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

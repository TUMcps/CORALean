module

public import CORALean.ContSet.Zonotope.Real.Theorems.CornerEqBottomAdd
public import CORALean.ContSet.Zonotope.Real.Theorems.SumFlipSucc
public import Mathlib.Tactic.Module
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The first block of the walk adds `2 g_k` at step `k`

`corner (j < k + 1) = corner (j < k) + 2 g_k`: the edge `[W_k; W_{k+1}]` of [1, Alg. 3] is
`[P; P + 2g]`.

## Inputs
* `Z` – planar zonotope
* `k` – generator index

## Hypotheses
* none

## Conclusion
* the next corner adds twice generator `k`

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.corner_succ_add (Z : Zonotope (Vec ℝ 2)) (k : Fin Z.h) :
    Z.corner (fun j => decide (j.val < k.val + 1))
      = Z.corner (fun j => decide (j.val < k.val)) + (2 : ℝ) • Z.G k := by
  rw [Zonotope.corner_eq_bottom_add, Zonotope.corner_eq_bottom_add, Zonotope.sum_flip_succ]
  module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

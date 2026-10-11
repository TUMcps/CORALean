import CORALean.ContSet.Zonotope.Real.Operations.BisectLow
import Mathlib.Analysis.Convex.Segment

/-!
# [1, Alg. 4], lines 1-28 with "smaller" in the printed order on both sides

`Zonotope.bisectLow` takes "smaller" in line 16 in the order in which the walk from the lowest
vertex meets the generators: increasing angle to the right, decreasing to the left. The listing
prints one order for both branches, the trigonometric one (increasing angle `Complex.arg`).
This is `bisectLow` with `SPLIT_PIVOT` read that way: the same lines, with the pass of lines
15-26 always run as `bisectStep γ true`, whose `splitPivot` compares by increasing angle, instead
of with `right`. On the left side it ends on the other boundary of the section
(`bisectLowPrinted_counterexample`).

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


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- [1, Alg. 4] lines 1-28 with line 16 taking "smaller" by increasing angle on both sides. -/
noncomputable def Zonotope.bisectLowPrinted (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) : ℝ :=
  let P := Z.c                                                         -- line 1
  let Z := Z.pointUp                                                   -- lines 3-6
  let P := P - ∑ i, Z.G i                                              -- lines 3, 7, 8
  let right := decide (P 0 < γ)                                        -- line 9
  let G := if right then Finset.univ.filter fun i => 0 < Z.G i 0       -- lines 10, 12
    else Finset.univ.filter fun i => Z.G i 0 < 0
  let s := ∑ i ∈ G, (2 : ℝ) • Z.G i                                    -- line 14
  let loop := (Z.bisectStep γ true)^[Z.h] (P, G, s)
  sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ loop.1 (loop.1 + loop.2.2)}  -- lines 27-28

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

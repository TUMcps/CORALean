module

public import CORALean.ContSet.Zonotope.Real.Operations.BisectLow
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

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

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- [1, Alg. 4] lines 1-28 with line 16 taking "smaller" by increasing angle on both sides. -/
noncomputable def Zonotope.bisectLowPrinted (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) : ℝ :=
  -- 1. the current position, `P ← c`
  let P := Z.c
  -- 3. lines 3-6: turn every generator upward
  let Z := Z.pointUp
  -- 7. lines 3, 7-8: `P ← P - gᵢ` drives `P` to the lowest vertex
  let P := P - ∑ i, Z.G i
  -- 9. look right if `x_P < γ`, left otherwise
  let right := decide (P 0 < γ)
  -- 10. lines 10-13: `G` is the generators pointing that way
  let G := if right then Finset.univ.filter fun i => 0 < Z.G i 0
    else Finset.univ.filter fun i => Z.G i 0 < 0
  -- 14. `s ← ∑_{g ∈ G} 2g`
  let s := ∑ i ∈ G, (2 : ℝ) • Z.G i
  -- 15. lines 15-26: `while |G| > 1`, with "smaller" by increasing angle on both sides
  let loop := (Z.bisectStep γ true)^[Z.h] (P, G, s)
  -- 27. lines 27-28: `(x, y) ← [P; P + s] ∩ L_γ`, `m ← y`
  sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ loop.1 (loop.1 + loop.2.2)}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

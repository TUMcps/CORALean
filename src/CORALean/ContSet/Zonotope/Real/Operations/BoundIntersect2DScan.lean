module

public import CORALean.ContSet.Zonotope.Real.Operations.ScanEdge
public import CORALean.ContSet.Zonotope.Real.Operations.PointUp
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# [1, Alg. 3]: `BOUND_INTERSECT_2D` by scanning

The zonogon `⟨c; g₁, …, g_r⟩` and the line `L_γ = {(x, y) | x = γ}`: turn the generators upward
(lines 3-6), drive `P` to the lowest vertex (lines 7-8), sort the generators by angle (line 9),
and scan the edges `[P; P + 2g]` up one chain (lines 10-17) and down the other (lines 18-25),
keeping the least and the greatest `y` at which an edge meets `L_γ`. `m = ∞` and `M = -∞` are
the starting values and the answer when nothing meets (line 2), so the pair is in `EReal`.

The "trigonometric order" is the angle `Complex.arg (x + i y)`, which is `0` for the zero
generator, and the sort is `Tuple.sort`; a loop `for j from 1 to r` is `Fin.foldl` over
`Fin r`.

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

/-- [1, Alg. 3]: the segment `[m; M]` with `{γ} × [m; M] = Z ∩ L_γ`. -/
noncomputable def Zonotope.boundIntersect2DScan (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) :
    EReal × EReal :=
  -- 1. the current position, `P ← c`
  let P := Z.c
  -- 2. `m ← ∞`, `M ← -∞`
  let mM : EReal × EReal := (⊤, ⊥)
  -- 3. lines 3-6: turn every generator upward
  let Z := Z.pointUp
  -- 7. lines 3, 7-8: `P ← P - gᵢ` drives `P` to the lowest vertex
  let P := P - ∑ i, Z.G i
  -- 9. sort the generators in trigonometric order, `g_{i₁}, …, g_{i_r}`
  let π := Tuple.sort fun i => Complex.arg ⟨Z.G i 0, Z.G i 1⟩
  let g := fun j => Z.G (π j)
  -- 10. lines 10-17: scan the edges `[P; P + 2g_{i_j}]` up one chain
  let up := Fin.foldl Z.h (fun s j =>
    (s.1 + (2 : ℝ) • g j, Zonotope.scanEdge γ s.1 (s.1 + (2 : ℝ) • g j) s.2)) (P, mM)
  -- 18. lines 18-25: and the edges `[P; P - 2g_{i_j}]` down the other
  let down := Fin.foldl Z.h (fun s j =>
    (s.1 - (2 : ℝ) • g j, Zonotope.scanEdge γ s.1 (s.1 - (2 : ℝ) • g j) s.2)) up
  -- 26. return `[m; M]`
  down.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

module

public import CORALean.ContSet.Zonotope.Real.Operations.BisectStep
public import CORALean.ContSet.Zonotope.Real.Operations.PointUp

@[expose] public section

/-!
# [1, Alg. 4], lines 1-28: the lower end of the section by bisection

Turn the generators upward (lines 3-6), drive `P` to the lowest vertex (lines 7-8), and look to the
right of it if `x_P < γ` and to the left otherwise (lines 9-13): `G` is the generators pointing
that way, `s` the sum `∑ 2g` of them, and `[P; P + s]` meets `L_γ`. Halve `G` by angle until one
generator remains (lines 14-26) and read `y` from the edge `[P; P + s]` (lines 27-28). Line 2,
`m ← ∞`, is overwritten at line 28 and not modelled. `while |G| > 1` is `bisectStep` iterated `r`
times, enough since each pass shrinks `G` and `|G| ≤ r`.

The set `G = {g₁, …, g_r} ∩ (ℝ₊ × ℝ)` is read with a strict sign, so vertical generators are in
neither side's `G`. The edge `[P; P + s]` meets `L_γ` in a point unless it is vertical or `G` is
empty, where `y` is the least point on it.

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
/-- [1, Alg. 4] lines 1-28: the least `y` with `(γ, y) ∈ Z`, for `Z ∩ L_γ` nonempty. -/
noncomputable def Zonotope.bisectLow (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) : ℝ :=
  let P := Z.c                                                         -- line 1
  let Z := Z.pointUp                                                   -- lines 3-6
  let P := P - ∑ i, Z.G i                                              -- lines 3, 7, 8
  let right := decide (P 0 < γ)                                        -- line 9
  let G := if right then Finset.univ.filter fun i => 0 < Z.G i 0       -- lines 10, 12
    else Finset.univ.filter fun i => Z.G i 0 < 0
  let s := ∑ i ∈ G, (2 : ℝ) • Z.G i                                    -- line 14
  let loop := (Z.bisectStep γ right)^[Z.h] (P, G, s)                   -- lines 15-26
  sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ loop.1 (loop.1 + loop.2.2)}  -- lines 27-28

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

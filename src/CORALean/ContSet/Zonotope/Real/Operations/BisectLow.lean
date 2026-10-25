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
times. `G` is read with a strict sign, so vertical generators are in neither side's `G`; the edge
meets `L_γ` unless it is vertical or `G` is empty, where `y` is the least point on it.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
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
  -- 1. the current position, `P ← c`
  let P := Z.c
  -- 3. lines 3-6: turn every generator upward
  let Z := Z.pointUp
  -- 7. lines 3, 7-8: `P ← P - gᵢ` drives `P` to the lowest vertex
  let P := P - ∑ i, Z.G i
  -- 9. look right if `x_P < γ`, left otherwise
  let right := decide (P 0 < γ)
  -- 10. lines 10-13: `G` is the generators pointing that way, `{g₁, …, g_r} ∩ (ℝ₊ × ℝ)` or `ℝ₋`
  let G := if right then Finset.univ.filter fun i => 0 < Z.G i 0
    else Finset.univ.filter fun i => Z.G i 0 < 0
  -- 14. `s ← ∑_{g ∈ G} 2g`
  let s := ∑ i ∈ G, (2 : ℝ) • Z.G i
  -- 15. lines 15-26: `while |G| > 1`, one `bisectStep` per pass
  let loop := (Z.bisectStep γ right)^[Z.h] (P, G, s)
  -- 27. lines 27-28: `(x, y) ← [P; P + s] ∩ L_γ`, `m ← y`
  sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ loop.1 (loop.1 + loop.2.2)}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

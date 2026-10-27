module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A planar zonotope mirrored in the x-axis

`(x, y) ↦ (x, -y)` on the center and the generators. Its lowest vertex is the highest vertex of
the original, which is how [1, Alg. 4] finds the upper end `M` of the section: "the same thing
starting from the upper vertex of `Z`" (line 29) is the lower search on the mirror image.

## Inputs
* `Z` – planar zonotope

## Output
* zonotope with the second coordinate negated

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z` with `y` negated throughout: the upper search of [1] is the lower one on it. -/
def Zonotope.mirrorY (Z : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) where
  h := Z.h
  c := ![Z.c 0, -Z.c 1]
  G := fun i => ![Z.G i 0, -Z.G i 1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

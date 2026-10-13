module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A planar zonotope mirrored in the x-axis

`(x, y) ↦ (x, -y)` on the centre and the generators. Its lowest vertex is the highest vertex of
the original, which is how [1, Alg. 4] finds the upper end `M` of the section: "the same thing
starting from the upper vertex of `Z`" (line 29) is the lower search on the mirror image.

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

/-- [1, Alg. 4]: `Z` with `y` negated throughout (line 29, the upper search). -/
def Zonotope.mirrorY (Z : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) where
  h := Z.h
  c := ![Z.c 0, -Z.c 1]
  G := fun i => ![Z.G i 0, -Z.G i 1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor
import Mathlib.Data.Fin.VecNotation

/-!
# A planar zonotope sheared along the x-axis

`(x, y) ↦ (x - κ y, y)` on the centre and the generators. It fixes the height of every point and
the direction of the x-axis, keeps the upper half-plane and the angle order of generators (the
cross product is unchanged), and takes the line `x - κ y = γ` to the vertical line `x = γ`. So the
section of `Z` by that line is the vertical section of the sheared zonogon, which is how the
boundary of a zonogon in the walk of [1, Alg. 3] is read off its vertical sections.

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

/-- [1, Alg. 3]: `Z` under `(x, y) ↦ (x - κ y, y)`. -/
def Zonotope.shear (κ : ℝ) (Z : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) where
  h := Z.h
  c := ![Z.c 0 - κ * Z.c 1, Z.c 1]
  G := fun i => ![Z.G i 0 - κ * Z.G i 1, Z.G i 1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

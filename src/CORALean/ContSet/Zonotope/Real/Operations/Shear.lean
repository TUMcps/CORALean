module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# A planar zonotope sheared along the x-axis

`(x, y) ↦ (x - κ y, y)` on the center and the generators. It fixes the height of every point and
the direction of the x-axis, keeps the upper half-plane and the angle order of generators (the
cross product is unchanged), and takes the line `x - κ y = γ` to the vertical line `x = γ`. So the
section of `Z` by that line is the vertical section of the sheared zonogon, which is how the
boundary of a zonogon in the walk of [1, Alg. 3] is read off its vertical sections.

## Inputs
* `κ` – shear factor
* `Z` – planar zonotope

## Output
* zonotope under the shear

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z` under `(x, y) ↦ (x - κ y, y)`, a tool for reading the scan of [1]. -/
def Zonotope.shear (κ : ℝ) (Z : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) where
  h := Z.h
  c := ![Z.c 0 - κ * Z.c 1, Z.c 1]
  G := fun i => ![Z.G i 0 - κ * Z.G i 1, Z.G i 1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

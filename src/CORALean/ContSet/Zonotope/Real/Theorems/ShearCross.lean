module

public import CORALean.ContSet.Zonotope.Real.Operations.Shear
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The shear keeps the cross product of the generators

`cross(S u, S v) = cross(u, v)` for the shear `S`, which has determinant `1`: sheared generators
are sorted by angle exactly when the originals are, so the walk of the sheared zonogon is the
sheared walk of [1, Alg. 3].

## Inputs
* `Z` – planar zonotope
* `κ` – shear factor
* `i` – first generator index
* `j` – second generator index

## Hypotheses
* none

## Conclusion
* the cross product of two generators is unchanged by the shear

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.shear_cross (Z : Zonotope (Vec ℝ 2)) (κ : ℝ) (i j : Fin Z.h) :
    (Z.shear κ).G i 0 * (Z.shear κ).G j 1 - (Z.shear κ).G i 1 * (Z.shear κ).G j 0
      = Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0 := by
  simp only [Zonotope.shear, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

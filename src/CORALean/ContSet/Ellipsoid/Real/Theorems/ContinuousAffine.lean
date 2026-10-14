module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# The map an ellipsoid is the image of is continuous

`u ↦ q + G *ᵥ u` coordinatewise, each coordinate a finite sum of products with a
constant. It carries compactness from the Euclidean unit ball onto the
ellipsoid, the same way `Zonotope.continuous_affine` carries it from the
coefficient cube.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.continuous_affine (E : Ellipsoid n) :
    Continuous fun u : Vec ℝ E.k => E.c + E.G *ᵥ u := by
  refine continuous_const.add (continuous_pi fun i => ?_)
  show Continuous fun u : Vec ℝ E.k => ∑ j, E.G i j * u j
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

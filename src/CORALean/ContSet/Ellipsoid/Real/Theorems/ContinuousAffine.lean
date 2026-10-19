module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic

@[expose] public section

/-!
# The map an ellipsoid is the image of is continuous

`u ↦ q + G *ᵥ u` coordinatewise, each coordinate a finite sum of products with a
constant. It carries compactness from the Euclidean unit ball onto the
ellipsoid, the same way `Zonotope.continuous_affine` carries it from the
coefficient cube.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* the map `u ↦ q + G u` is continuous
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.continuous_affine (E : Ellipsoid n) :
    Continuous fun u : Vec ℝ n => E.q + E.G *ᵥ u := by
  refine continuous_const.add (continuous_pi fun i => ?_)
  show Continuous fun u : Vec ℝ n => ∑ j, E.G i j * u j
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

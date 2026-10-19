module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage

@[expose] public section

/-!
# An ellipsoid is convex

An affine image of the Euclidean unit ball, and that ball is convex by the
triangle inequality, so nothing here is specific to ellipsoids beyond
`construct_eq_image`.

What the reachability theorems consume: an integral valued in the set needs it,
and it holds whatever `G` is, degenerate ones included.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* `E` is convex
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.convex_construct (E : Ellipsoid n) : Convex ℝ E.construct := by -- --- PROOF ---
  have himg : (fun u : Vec ℝ n => E.q + E.G *ᵥ u) '' unitBall₂ n
      = (fun z : Vec ℝ n => E.q + z) '' (Matrix.mulVecLin E.G '' unitBall₂ n) := by
    simp only [Set.image_image, Matrix.mulVecLin_apply]
  rw [E.construct_eq_image, himg]
  exact (convex_unitBall₂.linear_image (Matrix.mulVecLin E.G)).translate E.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --

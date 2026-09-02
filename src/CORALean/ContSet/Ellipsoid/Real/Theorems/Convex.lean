import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# An ellipsoid is convex

An affine image of the Euclidean unit ball, and that ball is convex by the
triangle inequality, so nothing here is specific to ellipsoids beyond
`construct_eq_image`.

What the reachability theorems consume: an integral valued in the set needs it,
and it holds whatever `G` is, degenerate ones included.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

theorem Ellipsoid.convex_construct (E : Ellipsoid n) : Convex ℝ E.construct := by
  have himg : (fun u : Vec ℝ E.k => E.q + E.G *ᵥ u) '' unitBall₂ E.k
      = (fun z : Vec ℝ n => E.q + z) '' (Matrix.mulVecLin E.G '' unitBall₂ E.k) := by
    simp only [Set.image_image, Matrix.mulVecLin_apply]
  rw [E.construct_eq_image, himg]
  exact (convex_unitBall₂.linear_image (Matrix.mulVecLin E.G)).translate E.q

end CORALean.Real

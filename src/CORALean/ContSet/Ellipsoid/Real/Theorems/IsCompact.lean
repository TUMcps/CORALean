import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# An ellipsoid is compact, hence closed

The Euclidean unit ball is compact — closed because `‖·‖₂` is continuous, and
inside the supremum-norm ball the ambient type carries because no coordinate
exceeds the whole — and the affine map onto the ellipsoid is continuous. As for
a zonotope, closedness comes this way rather than directly: an affine image of a
merely closed set need not be closed.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

theorem Ellipsoid.continuous_affine (E : Ellipsoid n) :
    Continuous fun u : Vec ℝ E.k => E.q + E.G *ᵥ u := by
  refine continuous_const.add (continuous_pi fun i => ?_)
  show Continuous fun u : Vec ℝ E.k => ∑ j, E.G i j * u j
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

theorem Ellipsoid.isCompact_construct (E : Ellipsoid n) : IsCompact E.construct := by
  rw [E.construct_eq_image]
  exact isCompact_unitBall₂.image E.continuous_affine

theorem Ellipsoid.isClosed_construct (E : Ellipsoid n) : IsClosed E.construct :=
  E.isCompact_construct.isClosed

end CORALean.Real
